-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed_dualNumber
-- name    : CerednikDrinfeld.FormalODModule.exists_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed_dualNumber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/bbd7d23f-1519-59d0-8716-fb131c68bd3a
-- title:
--   Two η_{i_0}-elements with 𝔽ₚ-independent tangent parts over κ[ε]
-- statement:
--   Let $p$ be a prime and $\kappa$ an algebraically closed field of characteristic $p$, let $j$ be a ring homomorphism from $\mathbb{W}(\mathbb{F}_{p^2})$ to the dual numbers $\kappa[\varepsilon]$, and let $X$ be a formal $\mathcal{O}_D$-module over $\kappa[\varepsilon]$, i.e. a two-dimensional commutative formal group law $F$ together with an action of $\mathbb{W}(\mathbb{F}_{p^2})$ by endomorphisms of $F$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$. Let $\gamma : \mathrm{Fin}\,2 \to \mathrm{CartierModule}\,p\,X.F$ be a homogeneous $V$-basis for $j$: each $\gamma_i$ lies in the graded piece `gradedPiece j i`, consisting of the $f$ with $\mathrm{endAct}(X.\mathrm{actEnd}(\tau(c)))f = \mathrm{homothety}(j(\tau(c))^{p^i})f$ for every $c \in \mathbb{F}_{p^2}$ (with $\tau$ the Teichmüller lift), and the matrix $(\mathrm{tangent}(\gamma_i)_k)$ has unit determinant; assume further that `gradedPiece j 0` and `gradedPiece j 1` are complementary subgroups, with complement datum $hc$. Let $a, \nu : \mathbb{N} \to \mathrm{Fin}\,2 \to \kappa$ and $c \in \kappa$ be such that $X$ has structure constants $a_{m,i} + c\,\nu_{m,i}\varepsilon$ relative to $\gamma$, meaning that for all $i$ and all $N$ there is $h$ with $\mathrm{endAct}(X.\varpi)(\gamma_i) = \sum_{m<N} V^{m}\bigl(\mathrm{homothety}(a_{m,i}+c\nu_{m,i}\varepsilon)\,\gamma_{\pi(m,i)}\bigr) + V^{N}h$, where $V$ is the integral Verschiebung and $\pi(m,i) \equiv m+i+1 \bmod 2$; assume $\nu_{0,i}=0$ for all $i$, and fix $i_0$ with $a_{0,i_0}=0$ and $a_{0,\pi(0,i_0)} \neq 0$. Assume that the reduction of $X$ along $\kappa[\varepsilon]\to\kappa$ has height $4$, that is, the kernel algebra of its multiplication-by-$p$ series is finite and projective with fibre dimension $p^4$ over every field. Finally let $L$ be an additive map from $M = \mathrm{CartierModule}\,p\,X.F$ to the module $\mathrm{NMod} = (M \times \Sigma)/\mathrm{nRel}$ of the graded Cartier module datum $D = X.\mathrm{toGradedCartierModuleData}\,j\,hc$, which is a canonical $L$-map: it is $\sigma$-semilinear, satisfies $L(Vx) = \mathrm{nMk}(\varpi x, 0)$ and $\lambda \circ L = \mathrm{frobenius}$, and descends from a Cartier $L$-map on a special lift of $D$ along a surjection with $p$-torsion-free-type kernel condition. Then there are $z_1, z_2$ in $D.\mathrm{etaPiece}\,L\,i_0$, the intersection of the subgroup `eta` attached to $L$ with the image under $\mathrm{nMk}$ of $D.\mathrm{piece}\,i_0 \times D.\mathrm{piece}\,i_0$, elements $m_1, m_2 \in M$ and $x_1, x_2 \in \kappa[\varepsilon]$ such that the class of $m_r$ in $M/VM$ equals the image of $z_r$ under the map `u` attached to $L$, such that $\mathrm{tangent}(m_r) = x_r \cdot \mathrm{tangent}(\gamma_{i_0})$, and such that the constant terms $\mathrm{fst}(x_1), \mathrm{fst}(x_2) \in \kappa$ are independent over $\mathbb{F}_p$: for all integers $c_1, c_2$ with $c_1\,\mathrm{fst}(x_1) + c_2\,\mathrm{fst}(x_2) = 0$ one has $p \mid c_1$ and $p \mid c_2$.
--
--   This is the independence statement for the $\mathbb{Z}_p$-structure of $\eta$ at a critical index over a first-order deformation $\kappa[\varepsilon]$ of an algebraically closed field: two elements of $\eta_{i_0}$ are produced whose tangent coordinates along $\gamma_{i_0}$ have $\mathbb{F}_p$-independent constant terms. It feeds the theorem [`CerednikDrinfeld.FormalODModule.not_exists_forall_period_variation_eq_mul_of_mem_etaPiece_of_hasStructureConstants_dualNumber`](thm.html#CerednikDrinfeld.FormalODModule.not_exists_forall_period_variation_eq_mul_of_mem_etaPiece_of_hasStructureConstants_dualNumber), in the Čerednik–Drinfel'd uniformisation part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed_dualNumber.lean

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

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

theorem CerednikDrinfeld.FormalODModule.exists_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed_dualNumber
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (j : Zp2 p →+* DualNumber κ) (X : FormalODModule p (DualNumber κ))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (a ν : ℕ → Fin 2 → κ) (c : κ)
    (hA : X.HasStructureConstants γ (fun m i => algebraMap κ (DualNumber κ) (a m i) + (c * ν m i) • DualNumber.eps))
    (hν0 : ∀ i, ν 0 i = 0) (i₀ : Fin 2) (ha0 : a 0 i₀ = 0)
    (ha1 : a 0 (FormalODModule.piIndex 0 i₀) ≠ 0)
    (hX4 : (X.map (TrivSqZeroExt.fstHom κ κ κ).toRingHom).HasHeight 4)
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) :
    ∃ (z₁ z₂ : (X.toGradedCartierModuleData j hc).NMod)
      (hz₁ : z₁ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀)
      (hz₂ : z₂ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀)
      (m₁ m₂ : CartierModule p X.F) (x₁ x₂ : DualNumber κ),
      (X.toGradedCartierModuleData j hc).vRange.mkQ m₁ =
        (X.toGradedCartierModuleData j hc).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁).1⟩ ∧
      (X.toGradedCartierModuleData j hc).vRange.mkQ m₂ =
        (X.toGradedCartierModuleData j hc).u L hL.isCartierLMap.map_verschiebung ⟨z₂, (AddSubgroup.mem_inf.mp hz₂).1⟩ ∧
      tangent m₁ = x₁ • tangent (γ i₀) ∧ tangent m₂ = x₂ • tangent (γ i₀) ∧
      ∀ c₁ c₂ : ℤ, c₁ • TrivSqZeroExt.fst x₁ + c₂ • TrivSqZeroExt.fst x₂ = 0 → (p : ℤ) ∣ c₁ ∧ (p : ℤ) ∣ c₂ := by sorry
