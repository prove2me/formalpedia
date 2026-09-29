-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_mem_etaPiece_one_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalODModule.exists_forall_mem_etaPiece_one_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/566678c4-b492-5811-87df-8f68635b9a9c
-- title:
--   Eta piece in degree one is a ℤₚ-lattice on invariants
-- statement:
--   Let $p$ be a prime, $K$ an algebraically closed field of characteristic $p$, and $j\colon W(\mathbb{F}_{p^2})\to K$ a ring homomorphism. Let $Y$ be a formal $\mathcal{O}_D$-module over $K$, i.e. a two-dimensional commutative formal group $Y.F$ together with an action of $W(\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$, assumed special with respect to $j$ (the two $j$-eigenspaces of the Lie algebra are complementary and invertible $K$-modules) and of height $4$ (the kernel of $[p]$ has degree $p^4$). Write $M=\mathrm{CartierModule}\,p\,Y.F$ and, for $n$, let $M_n$ be the subgroup of those $f\in M$ on which the Teichmüller action of each $c\in\mathbb{F}_{p^2}$ acts as the homothety by $j(\tau(c))^{p^n}$; assume $M_0$ and $M_1$ are complementary, giving the graded Cartier module data $D=Y.\mathrm{toGradedCartierModuleData}\,j\,hc$ with $F$, $V$, $\Pi$ the maps induced by Frobenius, Verschiebung and $\varpi$. Let $L\colon M\to D.\mathrm{NMod}=(M\times D.\mathrm{Sigma})/D.\mathrm{nRel}$ be an additive map satisfying the predicate `IsCanonicalLMap` (a Cartier $L$-map admitting a lift along a surjection from a $p$-torsion-free ring carrying a special graded Cartier module data), assume index $1$ is critical, i.e. $\Pi m\in V M$ for all $m\in M_1$, and let $c\colon\mathbb{Z}_p\to W(K)$ be any ring homomorphism. Then there exist $e_0,e_1\in M$ such that each $e_r$ lies in $M_1$ and satisfies $\Pi e_r=V e_r$; every $m\in M_1$ is uniquely of the form $\sum_r w_r\cdot e_r$ with $w\in W(K)^2$; an element $z$ of $D.\mathrm{NMod}$ lies in $D.\mathrm{etaPiece}\,L\,(\,L\circ V=\mathrm{nMk}(\Pi\cdot,0)\,)\,1$, the intersection of the subgroup `eta` attached to $L$ with the degree-$1$ piece, precisely when $z=\mathrm{nMk}(\sum_r c(a_r)\cdot e_r,\,0)$ for some $a\in\mathbb{Z}_p^2$; and distinct $a\in\mathbb{Z}_p^2$ give distinct such classes.
--
--   This identifies, at the critical index $1$, the degree-one part of the subgroup $\eta(L)$ of the $N$-module as a free $\mathbb{Z}_p$-module of rank $2$, spanned by the image of a $W(K)$-basis of $M_1$ consisting of elements with $\Pi e=V e$; it is the degree-one counterpart of the corresponding statement in degree $0$. It feeds the construction of rigidifications and of the tangent-space computations in the Čerednik–Drinfeld uniformisation, being cited in the passage from the $\eta$-lattice to explicit bases and matrix descriptions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_forall_mem_etaPiece_one_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.exists_forall_mem_etaPiece_one_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (Y : FormalODModule p K) (hY : Y.IsSpecial j) (hY4 : Y.HasHeight 4)
    (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (L : (Y.toGradedCartierModuleData j hc).M →+ (Y.toGradedCartierModuleData j hc).NMod)
    (hL : (Y.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (h1 : FormalODModule.CritChart.IsCritical Y j 1)
    (c : ℤ_[p] →+* WittVector p K) :
    ∃ e : Fin 2 → MvFormalGroup.CartierModule p Y.F,
      (∀ r, e r ∈ FormalODModule.CritChart.invariants Y j 1) ∧
      (∀ m ∈ Y.gradedPiece j 1, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e r) ∧
      (∀ z, z ∈ (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1 ↔
        ∃ a : Fin 2 → ℤ_[p], z = (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • e r, 0)) ∧
      (∀ a a' : Fin 2 → ℤ_[p],
        (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • e r, 0) =
          (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a' r) • e r, 0) → a = a') := by sorry
