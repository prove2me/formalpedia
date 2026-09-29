-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq
-- name    : CerednikDrinfeld.GradedCartierModuleData.eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/7275f752-a34c-5baf-a4c0-75c282e2970a
-- title:
--   Uniqueness of V-compatible semilinear maps on a homogeneous V-basis
-- statement:
--   Let $p$ be a prime, let $R$ and $B'$ be commutative rings equipped with ring homomorphisms $jR$ and $j'$ from $\mathrm{Zp2}\,p = W(\mathbb{F}_{p^2})$, and let $\varphi\colon R\to B'$ be a ring homomorphism. Let $D$ be a graded Cartier module datum over $(R,jR)$ and $D'$ one over $(B',j')$, each consisting of a module over the Witt vectors of the base ring together with additive endomorphisms $F$, $V$, a linear $\varpi$ and a two-term grading satisfying the usual Cartier relations. Assume $D'$ satisfies `IsSpecialCartierModule`: it possesses a homogeneous $V$-basis, and it is $V$-adically complete in the sense that for every sequence $(x_m)_{m\in\mathbb{N}}$ in $D'.M$ there is a unique $s$ such that for each $N$ one has $s = \sum_{m<N} V^m(x_m) + V^N t$ for some $t$. Let $\gamma\colon \mathrm{Fin}\,2\to D.M$ be a homogeneous $V$-basis of $D$, i.e. $\gamma_i$ lies in the $i$-th graded piece and every $x\in D.M$ is uniquely of the form $\sum_i [c_i]\,\gamma_i + V y$ with $c\in R^2$ (Teichmüller lifts) and $y\in D.M$. Let $\delta_1,\delta_2\colon D.M\to D'.M$ be additive maps, each satisfying $\delta(w\cdot x) = W(\varphi)(w)\cdot\delta(x)$ for all $w\in W(p,R)$, $x\in D.M$, and $\delta(Vx) = V(\delta x)$. If $\delta_1(\gamma_i) = \delta_2(\gamma_i)$ for $i=0,1$, then $\delta_1 = \delta_2$.
--
--   This is the uniqueness half of the universal property of the completed base change of a graded Cartier module along $\varphi$: a Witt-semilinear, $V$-commuting map out of a module with a homogeneous $V$-basis is determined by its values on that basis. It is used in the construction of the base-change morphism and in the statement of its existence-and-uniqueness property.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq
    (p : ℕ) [Fact p.Prime] {R B' : Type} [CommRing R] [CommRing B']
    {jR : CerednikDrinfeld.Zp2 p →+* R} {j' : CerednikDrinfeld.Zp2 p →+* B'} (φ : R →+* B')
    (D : CerednikDrinfeld.GradedCartierModuleData p R jR)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (δ₁ δ₂ : D.M →+ D'.M)
    (h₁ : ∀ (w : WittVector p R) (x : D.M), δ₁ (w • x) = WittVector.map φ w • δ₁ x)
    (h₁V : ∀ x : D.M, δ₁ (D.verschiebung x) = D'.verschiebung (δ₁ x))
    (h₂ : ∀ (w : WittVector p R) (x : D.M), δ₂ (w • x) = WittVector.map φ w • δ₂ x)
    (h₂V : ∀ x : D.M, δ₂ (D.verschiebung x) = D'.verschiebung (δ₂ x))
    (hγeq : ∀ i : Fin 2, δ₁ (γ i) = δ₂ (γ i)) :
    δ₁ = δ₂ := by sorry
