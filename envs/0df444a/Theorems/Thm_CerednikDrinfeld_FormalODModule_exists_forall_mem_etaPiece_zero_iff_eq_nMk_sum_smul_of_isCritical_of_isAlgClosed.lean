-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_mem_etaPiece_zero_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalODModule.exists_forall_mem_etaPiece_zero_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/0eeea912-8c83-5981-bf94-7b2b659726c0
-- title:
--   η₀(L) as a ℤₚ-lattice at a critical index
-- statement:
--   Let $p$ be a prime and $K$ an algebraically closed field of characteristic $p$, let $j$ be a ring homomorphism from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ to $K$, and let $Y$ be a formal $\mathcal{O}_D$-module over $K$: a two-dimensional commutative formal group law $Y.F$ together with an action of $\mathbb{Z}_{p^2}$ by endomorphisms and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$. Assume $Y$ is special for $j$ (the two $j$-eigenspaces of the Lie algebra are complementary and each invertible over $K$), that $[p]$ has kernel of degree $p^4$, and that the graded pieces $M_0$ and $M_1$ of the Cartier module $M =$ `CartierModule p Y.F` are complementary, where $M_n$ consists of those $f$ with $[\zeta]_* f = j(\zeta)^{p^n} f$ for every Teichmüller lift $\zeta$ of an element of $\mathbb{F}_{p^2}$; let $D$ be the resulting graded Cartier module datum, $L : M \to \mathrm{NMod}(D)$ an additive map which is a canonical $L$-map, and assume index $0$ is critical, i.e. $\varpi_* m \in V(M)$ for every $m \in M_0$. Finally let $c : \mathbb{Z}_p \to W(K)$ be any ring homomorphism. Then there exists $e : \{0,1\} \to M$ such that each $e_r$ lies in $M_0$ and satisfies $\varpi_* e_r = V e_r$; every $m \in M_0$ is uniquely of the form $\sum_r w_r \cdot e_r$ with $w : \{0,1\} \to W(K)$; an element $z$ of $\mathrm{NMod}(D)$ lies in the degree-$0$ piece $\eta(L) \cap N_0$ (formed using the identity $L(Vx) = [(\varpi_* x, 0)]$ coming from $L$ being a Cartier $L$-map) if and only if $z = [(\sum_r c(a_r)\cdot e_r, 0)]$ for some $a : \{0,1\} \to \mathbb{Z}_p$; and the map $a \mapsto [(\sum_r c(a_r)\cdot e_r, 0)]$ is injective.
--
--   This identifies the degree-$0$ part of the $\eta$-construction attached to a canonical $L$-map as a free $\mathbb{Z}_p$-module of rank $2$ inside $\mathrm{NMod}(D)$, with an explicit basis consisting of $\varpi = V$ invariants that is simultaneously a $W(K)$-basis of $M_0$; it is the lattice used in the local theory of special formal $\mathcal{O}_D$-modules underlying the Čerednik–Drinfeld uniformisation. It is invoked in the determinant and rigidification computations for such modules, and in the study of the tangent vectors of $\eta_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_forall_mem_etaPiece_zero_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_forall_mem_etaPiece_zero_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (Y : FormalODModule p K) (hY : Y.IsSpecial j) (hY4 : Y.HasHeight 4)
    (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (L : (Y.toGradedCartierModuleData j hc).M →+ (Y.toGradedCartierModuleData j hc).NMod)
    (hL : (Y.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (h0 : FormalODModule.CritChart.IsCritical Y j 0)
    (c : ℤ_[p] →+* WittVector p K) :
    ∃ e : Fin 2 → MvFormalGroup.CartierModule p Y.F,
      (∀ r, e r ∈ FormalODModule.CritChart.invariants Y j 0) ∧
      (∀ m ∈ Y.gradedPiece j 0, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e r) ∧
      (∀ z, z ∈ (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0 ↔
        ∃ a : Fin 2 → ℤ_[p], z = (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • e r, 0)) ∧
      (∀ a a' : Fin 2 → ℤ_[p],
        (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • e r, 0) =
          (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a' r) • e r, 0) → a = a') := by sorry
