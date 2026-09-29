-- Prove2me | Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq
-- name    : AlgebraicGeometry.ThetaLevel.exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/1ec34673-6f60-594b-8a1a-90dc94863c06
-- title:
--   ε-intertwiners are unit multiples of the chosen intertwiner
-- statement:
--   Fix $g$ and $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta_i$ nonzero, an $N$ with $\prod_i \delta_i = N+1$, and a bijection $e$ between $\mathrm{Fin}(N+1)$ and $H(\delta) = \prod_i \mathbb{Z}/\delta_i$. Let $B$ be a commutative ring in which $N+1$ is invertible, and let $\zeta, \omega \in B$ satisfy $\zeta^{N+1} = 1$, $1 - \zeta^{j}$ a unit for $0 < j < N+1$, and $\omega^{2} = \zeta$. Here $\mathrm{Heis}\,\delta\,(N+1)$ consists of triples $(a,h,k)$ with $a \in \mathbb{Z}/2(N+1)$ and $h,k \in H(\delta)$, the Schrödinger matrix `schrodMat` of $z$ has $(i,j)$ entry $\omega^{(z.a + \sum_i \iota(z.k_i (e j)_i)).\mathrm{val}}$ when $e i = e j + z.h$ and $0$ otherwise, and $\Gamma =$ `Heis.Gam` is the group of automorphisms of $\mathrm{Heis}\,\delta\,(N+1)$ fixing each central element; assume every $\gamma \in \Gamma$ admits an invertible $U$ over $B$ with $U\,\vartheta(z) = \vartheta(\gamma z)\,U$ for all $z$, so that the chosen matrix $\mathrm{inter}(\gamma)$ is such a $U$. Let $\varphi_B : B \to S$ be a ring homomorphism into a commutative ring $S$, $T$ an invertible $(N+1)\times(N+1)$ matrix over $S$, $\varepsilon \in S$ idempotent, and $\gamma \in \Gamma$ with $\varepsilon \cdot (T\,\vartheta_S(z)) = \varepsilon \cdot (\vartheta_S(\gamma z)\,T)$ for all $z$, where $\vartheta_S$ is the Schrödinger matrix formed over $S$ with $\varphi_B(\omega)$. Then there is a unit $c \in S^\times$ with $\varepsilon \cdot T = \varepsilon \cdot \bigl(c \cdot \varphi_B(\mathrm{inter}(\gamma))\bigr)$, the homomorphism being applied entrywise.
--
--   This is the Schur-type rigidity step for the Schrödinger representation of the finite Heisenberg group attached to $\delta$: after localising at an idempotent, any invertible matrix intertwining $\vartheta$ with its $\gamma$-twist agrees with a unit scalar multiple of the canonically chosen intertwiner $\mathrm{inter}(\gamma)$. It is used in [`AlgebraicGeometry.ThetaLevel.exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq`](thm.html#AlgebraicGeometry.ThetaLevel.exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq), the comparison of theta-level structures over a base in which the relevant roots of unity behave well.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ThetaLevel_exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq.lean

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    (hint : ∀ γ : (Heis.Gam (δ := δ) (d := N + 1)), ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) B, IsIntertwiner δ (N + 1) B ω e γ.1 U)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (ε : S) (hε : IsIdempotentElem ε)
    (γ : (Heis.Gam (δ := δ) (d := N + 1)))
    (hγ : ∀ z : Heis δ (N + 1), ε • (T * schrodMat δ (N + 1) S (φB ω) e z) =
      ε • (schrodMat δ (N + 1) S (φB ω) e (γ.1 z) * T)) :
    ∃ c : Sˣ, ε • T = ε • ((c : S) • (ThetaLevel.inter δ (N + 1) B ω e γ.1).map φB) := by sorry
