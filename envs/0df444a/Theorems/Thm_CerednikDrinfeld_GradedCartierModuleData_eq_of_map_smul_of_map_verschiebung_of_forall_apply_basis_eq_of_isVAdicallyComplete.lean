-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete
-- name    : CerednikDrinfeld.GradedCartierModuleData.eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/7e3484df-ec6f-5644-9034-20f3c0a1d5ee
-- title:
--   Uniqueness of V-compatible semilinear maps on a homogeneous V-basis
-- statement:
--   Fix a prime $p$ and commutative rings $R$, $B'$ equipped with ring maps $j_R, j'$ from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$, let $\varphi\colon R \to B'$ be a ring homomorphism, and let $D$, $D'$ be graded Cartier module data over $(R,j_R)$ and $(B',j')$ respectively; thus each consists of a module $M$ over the Witt vectors of the base together with additive maps $F$, $V$, a linear operator $\varpi$ and a pair of complementary submodules $\mathrm{piece}\,0$, $\mathrm{piece}\,1$ satisfying the usual Cartier relations and shifting the grading by one. Assume $D'$ is $V$-adically complete, i.e. for every sequence $(x_m)_{m \in \mathbb{N}}$ in $M_{D'}$ there is a unique $s \in M_{D'}$ such that for every $N$ one has $s = \sum_{m<N} V^m(x_m) + V^N t$ for some $t$. Let $\gamma\colon \mathrm{Fin}\,2 \to M_D$ be a homogeneous $V$-basis, i.e. $\gamma_i \in \mathrm{piece}\,i$ and every $x \in M_D$ is uniquely of the form $\sum_i [c_i]\,\gamma_i + V y$ with $c \in R^{2}$, $y \in M_D$, where $[\,\cdot\,]$ is the Teichmüller lift. Let $\delta_1, \delta_2\colon M_D \to M_{D'}$ be additive maps, each $\varphi$-semilinear in the sense that $\delta(w \cdot x) = W(\varphi)(w) \cdot \delta(x)$ for all Witt vectors $w$ over $R$ and all $x$, and each commuting with $V$. If $\delta_1(\gamma_i) = \delta_2(\gamma_i)$ for $i = 0,1$, then $\delta_1 = \delta_2$.
--
--   A rigidity statement in the Cartier-theoretic description of special formal $\mathcal{O}_D$-modules: a semilinear, $V$-equivariant map out of a Cartier module with a homogeneous $V$-basis is determined by its values on that basis, provided the target is $V$-adically complete. It is the form of the uniqueness principle needed when the target carries no global homogeneous $V$-basis, and it is used in the proof that rigidified special formal modules admit the required comparison of $n$-maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.GradedCartierModuleData.eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete
    (p : ℕ) [Fact p.Prime] {R B' : Type} [CommRing R] [CommRing B']
    {jR : CerednikDrinfeld.Zp2 p →+* R} {j' : CerednikDrinfeld.Zp2 p →+* B'} (φ : R →+* B')
    (D : CerednikDrinfeld.GradedCartierModuleData p R jR)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsVAdicallyComplete)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (δ₁ δ₂ : D.M →+ D'.M)
    (h₁ : ∀ (w : WittVector p R) (x : D.M), δ₁ (w • x) = WittVector.map φ w • δ₁ x)
    (h₁V : ∀ x : D.M, δ₁ (D.verschiebung x) = D'.verschiebung (δ₁ x))
    (h₂ : ∀ (w : WittVector p R) (x : D.M), δ₂ (w • x) = WittVector.map φ w • δ₂ x)
    (h₂V : ∀ x : D.M, δ₂ (D.verschiebung x) = D'.verschiebung (δ₂ x))
    (hγeq : ∀ i : Fin 2, δ₁ (γ i) = δ₂ (γ i)) :
    δ₁ = δ₂ := by sorry
