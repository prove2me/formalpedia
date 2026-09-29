-- Prove2me | Theorems.Thm_CerednikDrinfeld_not_dvd_natCard_of_le_map_quaternion_units_of_prime_of_five_le
-- name    : CerednikDrinfeld.not_dvd_natCard_of_le_map_quaternion_units_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/6cff29c8-ec3a-5abb-acb1-533c874f9436
-- title:
--   No p-torsion for p≥ 5 in finite subgroups of ρ(H^×)
-- statement:
--   Let $K_0$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $a,b\in\mathbb{Q}$, and let $\mathbb{H}[\mathbb{Q},a,b]$ be the associated rational quaternion algebra. Suppose given a $\mathbb{Q}$-algebra homomorphism $\iota \colon \mathbb{H}[\mathbb{Q},a,b] \to M_2(K_0)$ and a group homomorphism $\rho$ from the unit group $\mathbb{H}[\mathbb{Q},a,b]^\times$ to $\mathrm{PGL}(2,K_0)$, subject to the hypothesis that $\rho$ is the projectivisation of $\iota$: for every unit $x$, $\rho(x)$ is the class in $\mathrm{PGL}(2,K_0)$, formed by `Matrix.ProjGenLinGroup.mk`, of the image of $x$ under the map on units induced by the multiplicative map underlying $\iota$. The assertion is then: for every natural number $p$ that is prime and satisfies $5 \le p$, and for every subgroup $H$ of $\mathrm{PGL}(2,K_0)$ which is contained in the image under $\rho$ of the full subgroup $\top$ of $\mathbb{H}[\mathbb{Q},a,b]^\times$ and which is finite, $p$ does not divide $\mathrm{Nat.card}\,H$, the cardinality of $H$. No definiteness assumption on the quaternion algebra and no injectivity assumption on $\iota$ are imposed.
--
--   This is the elementary torsion bound for $\mathbb{H}^\times/\mathbb{Q}^\times$: an element of $\mathbb{H}[\mathbb{Q},a,b]^\times$ whose image in $\mathrm{PGL}_2$ has prime order generates a quadratic extension of $\mathbb{Q}$ containing a $p$-th root of unity, which forces $p \le 3$. It is used in the Čerednik–Drinfeld part of the development to control stabilisers of vertices in the coset graph attached to a quaternionic unit group, where finiteness together with order prime to $p$ is what makes the local arguments at $p$ go through.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_not_dvd_natCard_of_le_map_quaternion_units_of_prime_of_five_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Quaternion

theorem CerednikDrinfeld.not_dvd_natCard_of_le_map_quaternion_units_of_prime_of_five_le
    (K₀ : Type) [Field K₀] [Algebra ℚ K₀]
    {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀)
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, K₀))
    (hρ : ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = Matrix.ProjGenLinGroup.mk
      (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) K₀) x)) :
    ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ H : Subgroup PGL(2, K₀),
      H ≤ (⊤ : Subgroup (ℍ[ℚ, a, b])ˣ).map ρ → Finite H → ¬ p ∣ Nat.card H := by sorry
