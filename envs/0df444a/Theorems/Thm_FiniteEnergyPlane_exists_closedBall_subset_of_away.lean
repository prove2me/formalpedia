-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_closedBall_subset_of_away
-- name    : FiniteEnergyPlane.exists_closedBall_subset_of_away
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T17:56:16.709009+00:00
-- url     : https://prove2.me/theorems/3eec7c63-d7af-45d3-982f-2389c7347734
-- title:
--   Uniform closed discs around points of an exhaustion of a punctured plane
-- statement:
--   Let $\Gamma\subset\mathbb C$ be finite and let $(U_k)_{k\in\mathbb N}$ be an increasing sequence of open subsets of $\mathbb C$ with $\bigcup_kU_k=\mathbb C\setminus\Gamma$. Let $z_k\in\mathbb C$ and $\delta>0$ with $|z_k-\gamma|\ge\delta$ for all $k$ and all $\gamma\in\Gamma$. Assume that either the sequence $(z_k)$ is bounded, or $\{w:|w|>R\}\subseteq U_m$ for some $m$ and some $R$. Then there are $\rho>0$ and $m\in\mathbb N$ such that
--   $$\overline B(z_k,\rho)\subseteq U_k\qquad\text{for all }k\ge m.$$
--
--   This gives a uniform amount of room around a sequence of points that stays away from the punctures, inside the domains of a sequence of curves defined on an exhaustion of $\mathbb C\setminus\Gamma$.
--
--   **Formalization Note** $\Gamma$ is a `Finset ℂ`, the exhaustion is `Monotone U` with `⋃ k, U k = (↑Γ)ᶜ`, and the discs are closed balls.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, proof of Lemma 2.20, p. 12; H. Hofer, Invent. Math. 114 (1993), Section 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Uniform room around points of an exhaustion of a finitely punctured plane. Let `Γ ⊆ ℂ` be
finite and `U_k` an increasing sequence of open sets with `⋃ U_k = ℂ \ Γ`. Let `z_k ∈ ℂ` stay at
distance `≥ δ > 0` from `Γ`, and assume that either `(z_k)` is bounded or some `U_m` contains
`{|w| > R}` for some `R`. Then there are `ρ > 0` and `m` such that `B̄(z_k, ρ) ⊆ U_k` for all
`k ≥ m`. -/
theorem exists_closedBall_subset_of_away (Γ : Finset ℂ) (U : ℕ → Set ℂ)
    (hUo : ∀ k, IsOpen (U k)) (hUmono : Monotone U) (hUunion : ⋃ k, U k = (↑Γ)ᶜ) (z : ℕ → ℂ)
    (haway : ∃ δ : ℝ, 0 < δ ∧ ∀ k, ∀ γ ∈ Γ, δ ≤ ‖z k - γ‖)
    (hbdd : (∃ R : ℝ, ∀ k, ‖z k‖ ≤ R) ∨ ∃ m : ℕ, ∃ R : ℝ, {w : ℂ | R < ‖w‖} ⊆ U m) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ m : ℕ, ∀ k, m ≤ k → closedBall (z k) ρ ⊆ U k := by
  sorry

end FiniteEnergyPlane
