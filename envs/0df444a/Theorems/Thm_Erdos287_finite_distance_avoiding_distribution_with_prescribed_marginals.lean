-- Prove2me | Theorems.Thm_Erdos287_finite_distance_avoiding_distribution_with_prescribed_marginals
-- name    : Erdos287.finite_distance_avoiding_distribution_with_prescribed_marginals
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:32:30.302635+00:00
-- url     : https://prove2.me/theorems/dcdacc61-d8e4-4cac-8ccb-be828edb2abe
-- title:
--   Distance-avoiding finite distribution with exact same-position marginals
-- statement:
--   Assign finitely many indices to integer positions, and let $u>0$, $v\ge0$, and $b\in[0,1]$. There is a finite probability distribution on sets of indices whose positions avoid pair distances in $[u,v]$. For every nonempty set $T$ of indices, the probability that every element of $T$ is selected is at most $(u/(u+v))b^{|T|}$, with equality if the indices in $T$ all have the same position.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Application to the grouped prime-occupancy reduction.

import Mathlib

theorem Erdos287.finite_distance_avoiding_distribution_with_prescribed_marginals {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℕ) (u v : ℕ) (hu : 0 < u) (b : ℝ) (hb : 0 ≤ b) (hb₁ : b ≤ 1) :
    ∃ (w : Fin (u + v) × (ι → Bool) → ℝ)
      (C : Fin (u + v) × (ι → Bool) → Finset ι),
      (∀ z, 0 ≤ w z) ∧ (∑ z, w z) = 1 ∧
      (∀ z i, i ∈ C z → ∀ j, j ∈ C z → g i ≤ g j →
        ¬ (u ≤ g j - g i ∧ g j - g i ≤ v)) ∧
      ∀ T : Finset ι, T.Nonempty →
        let mass := ∑ z ∈ Finset.univ.filter (fun z => T ⊆ C z), w z
        let bound := ((u : ℝ) / ((u + v : ℕ) : ℝ)) * b ^ T.card
        mass ≤ bound ∧ ((∀ i ∈ T, ∀ j ∈ T, g i = g j) → mass = bound) := by sorry
