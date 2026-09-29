-- Prove2me | Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq
-- name    : AlgebraicGeometry.ThetaLevel.exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/f36158c0-ee65-5636-8ddc-e0cdfc35f55b
-- title:
--   Conjugating relabelling arises from a centre-fixing Heisenberg automorphism
-- statement:
--   Fix $g$ and $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta_i$ nonzero, and $N$ with $\prod_i \delta_i = N+1$; fix a bijection $e$ between $\mathrm{Fin}(N+1)$ and $H(\delta) = \prod_i \mathbb{Z}/\delta_i$. Let $B$ be a commutative ring in which $N+1$ is a unit, carrying $\zeta$ with $\zeta^{N+1} = 1$ such that $1 - \zeta^{j}$ is a unit for every $0 < j < N+1$, and $\omega$ with $\omega^2 = \zeta$. Let $S$ be a commutative ring, $\varphi_B : B \to S$ a ring homomorphism, $T$ an invertible $(N+1)\times(N+1)$ matrix over $S$, $\varepsilon \in S$ idempotent. Write $\vartheta(z) =$ `schrodMat` $\delta\,(N+1)\,S\,(\varphi_B\omega)\,e\,z$ for $z = (a,h,k)$ in the Heisenberg set $\mathrm{Heis}\,\delta\,(N+1)$, the matrix whose $(i,j)$ entry is $(\varphi_B\omega)^{(a + \mathrm{pair}(k, e_j)).\mathrm{val}}$ when $e_i = e_j + h$ and $0$ otherwise, with $\mathrm{pair}(k,h) = \sum_i \iota_i(k_i h_i) \in \mathbb{Z}/2(N+1)$. Assume given an arbitrary map $w$ of $\mathrm{Heis}\,\delta\,(N+1)$ to itself with $\varepsilon\,T\vartheta(z) = \varepsilon\,\vartheta(w z)\,T$ (entrywise scaling) for all $z$. Then there is $\gamma$ in $\mathrm{Gam}$, the subgroup of multiplicative automorphisms of $\mathrm{Heis}\,\delta\,(N+1)$ fixing every central element $\mathrm{cen}\,a$, with $\varepsilon\,T\vartheta(z) = \varepsilon\,\vartheta(\gamma z)\,T$ for all $z$.
--
--   This is the step, in the theory of theta structures, that upgrades a bare relabelling map realised by conjugating the Schrödinger representation on an idempotent piece into an automorphism of the finite Heisenberg group acting trivially on the centre, i.e. an element of $\Gamma_\delta$. It feeds the construction of idempotents, centre-fixing automorphisms and units in `exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ThetaLevel_exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq.lean

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (ε : S) (hε : IsIdempotentElem ε)
    (w : Heis δ (N + 1) → Heis δ (N + 1))
    (hw : ∀ z : Heis δ (N + 1), ε • (T * schrodMat δ (N + 1) S (φB ω) e z) =
      ε • (schrodMat δ (N + 1) S (φB ω) e (w z) * T)) :
    ∃ γ : (Heis.Gam (δ := δ) (d := N + 1)),
      ∀ z : Heis δ (N + 1), ε • (T * schrodMat δ (N + 1) S (φB ω) e z) =
        ε • (schrodMat δ (N + 1) S (φB ω) e (γ.1 z) * T) := by sorry
