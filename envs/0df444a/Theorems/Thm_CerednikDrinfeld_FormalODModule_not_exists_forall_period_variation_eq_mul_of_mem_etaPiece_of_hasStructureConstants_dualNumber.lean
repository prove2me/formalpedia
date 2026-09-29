-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_not_exists_forall_period_variation_eq_mul_of_mem_etaPiece_of_hasStructureConstants_dualNumber
-- name    : CerednikDrinfeld.FormalODModule.not_exists_forall_period_variation_eq_mul_of_mem_etaPiece_of_hasStructureConstants_dualNumber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/75dde8f4-a287-5acd-802b-095d1a5c7216
-- title:
--   Tangent variation on η_{i_0} is no rescaling outside windows
-- statement:
--   Let $p$ be a prime and $\kappa$ an algebraically closed field of characteristic $p$, let $j:\mathbb{W}(\mathbb{F}_{p^2})\to\kappa[\varepsilon]$ be a ring homomorphism into the dual numbers, and let $X$ be a formal $\mathcal{O}_D$-module over $\kappa[\varepsilon]$ (a $2$-dimensional commutative formal group law with a $\mathbb{W}(\mathbb{F}_{p^2})$-action and an endomorphism $\varpi$ with $\varpi^2=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$). Let $\gamma:\mathrm{Fin}\,2\to C(X)$ be a homogeneous $V$-basis of the Cartier module, i.e. $\gamma_i$ lies in the $i$-th graded piece (eigenspace condition $[\tau c]\cdot f=\langle j(\tau c)^{p^i}\rangle f$ for all $c\in\mathbb{F}_{p^2}$) and the matrix of tangent vectors of the $\gamma_i$ has unit determinant; let $hc$ assert that the pieces of degrees $0$ and $1$ are complementary. Assume $X$ has structure constants $m\mapsto a_{m,i}+\varepsilon c\,\nu_{m,i}$ with respect to $\gamma$, i.e. for all $i$ and $N$, $\varpi\cdot\gamma_i=\sum_{m<N}V^m\big(\langle a_{m,i}+\varepsilon c\nu_{m,i}\rangle\gamma_{\pi(m,i)}\big)+V^N h$ for some $h$, where $\pi(m,i)=(m+i+1)\bmod 2$ and $V$ is the integral Verschiebung; assume $\nu_{0,i}=0$ for all $i$, and fix $i_0$ with $a_{0,i_0}=0$ and $A:=a_{0,\pi(0,i_0)}\neq 0$. Assume the reduction of $X$ along $\kappa[\varepsilon]\to\kappa$ has height $4$, i.e. the kernel algebra of its $[p]$-action is finite projective with fibre dimension $p^4$. Assume the window condition: there are no $c_1,c_2\in\kappa$ with $\nu_{1,i_0}=c_1A-c_2a_{1,i_0}$, $\nu_{1,\pi(0,i_0)}=-c_1A^{p}-c_2a_{1,\pi(0,i_0)}$ and $\nu_{2,i_0}=-c_1a_{1,i_0}^{p}-c_2a_{2,i_0}$. Finally let $L$ be an additive map from $C(X)$ to the associated $N$-module which is a canonical $L$-map (Cartier: $\sigma$-semilinear, $L(Vx)=\overline{(\varpi x,0)}$, $\lambda\circ L=F$, together with a lift of the prescribed kind over a $p$-torsion-free surjection onto $\kappa[\varepsilon]$ with special Cartier module). Then there is no $\mu\in\kappa$ such that for every $z$ in the $i_0$-component $\eta(L)\cap N_{i_0}$, every $m\in C(X)$ whose class modulo $V\,C(X)$ equals $u(L)(z)$, and every $x\in\kappa[\varepsilon]$ with $\mathrm{tangent}(m)=x\cdot\mathrm{tangent}(\gamma_{i_0})$, writing $y$ for the $\kappa$-part of $x$, one has $(A^{p+1}\nu_{2,i_0}-A\,a_{1,i_0}^{p}\nu_{1,\pi(0,i_0)})\,y^{p^2}+(A^{p}\nu_{1,i_0}+A\,\nu_{1,\pi(0,i_0)})\,y^{p}=\mu y$.
--
--   This is the non-degeneracy step in the Čerednik–Drinfeld analysis of first-order deformations of special formal $\mathcal{O}_D$-modules at a smooth point: the $\varepsilon$-variation of the tangent coordinate along the line $\eta_{i_0}$ is not a scalar rescaling of that coordinate unless the deformation direction $\nu$ comes from a change of homogeneous $V$-basis. It is used in the comparison of two such lines, via [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.isIsomorphic_of_line_transport_of_not_node`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.isIsomorphic_of_line_transport_of_not_node).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_not_exists_forall_period_variation_eq_mul_of_mem_etaPiece_of_hasStructureConstants_dualNumber.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvFormalGroup MvFormalGroup.CartierModule
open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.not_exists_forall_period_variation_eq_mul_of_mem_etaPiece_of_hasStructureConstants_dualNumber
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (j : Zp2 p →+* DualNumber κ) (X : FormalODModule p (DualNumber κ))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (a ν : ℕ → Fin 2 → κ) (c : κ)
    (hA : X.HasStructureConstants γ (fun m i => algebraMap κ (DualNumber κ) (a m i) + (c * ν m i) • DualNumber.eps))
    (hν0 : ∀ i, ν 0 i = 0) (i₀ : Fin 2) (ha0 : a 0 i₀ = 0)
    (ha1 : a 0 (FormalODModule.piIndex 0 i₀) ≠ 0)
    (hX4 : (X.map (TrivSqZeroExt.fstHom κ κ κ).toRingHom).HasHeight 4)
    (hwin : ∀ c₁ c₂ : κ,
      ¬ (ν 1 i₀ = c₁ * a 0 (FormalODModule.piIndex 0 i₀) - c₂ * a 1 i₀ ∧
         ν 1 (FormalODModule.piIndex 0 i₀) = -(c₁ * a 0 (FormalODModule.piIndex 0 i₀) ^ p) - c₂ * a 1 (FormalODModule.piIndex 0 i₀) ∧
         ν 2 i₀ = -(c₁ * a 1 i₀ ^ p) - c₂ * a 2 i₀))
    (L : (X.toGradedCartierModuleData j hc).M →+
      (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) :
    ¬ ∃ μ : κ, ∀ (z : (X.toGradedCartierModuleData j hc).NMod)
      (hz : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L
        hL.isCartierLMap.map_verschiebung i₀)
      (m : CartierModule p X.F)
      (hm : (X.toGradedCartierModuleData j hc).vRange.mkQ m =
        (X.toGradedCartierModuleData j hc).u L
          hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz).1⟩)
      (x : DualNumber κ), tangent m = x • tangent (γ i₀) →
      (a 0 (FormalODModule.piIndex 0 i₀) ^ (p + 1) * ν 2 i₀ -
          a 0 (FormalODModule.piIndex 0 i₀) * a 1 i₀ ^ p * ν 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst x ^ (p ^ 2) +
        (a 0 (FormalODModule.piIndex 0 i₀) ^ p * ν 1 i₀ + a 0 (FormalODModule.piIndex 0 i₀) * ν 1 (FormalODModule.piIndex 0 i₀)) *
          TrivSqZeroExt.fst x ^ p =
      μ * TrivSqZeroExt.fst x := by sorry
