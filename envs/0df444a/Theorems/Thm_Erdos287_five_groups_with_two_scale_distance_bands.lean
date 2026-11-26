-- Prove2me | Theorems.Thm_Erdos287_five_groups_with_two_scale_distance_bands
-- name    : Erdos287.five_groups_with_two_scale_distance_bands
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T09:11:25.131059+00:00
-- url     : https://prove2.me/theorems/46365492-7f1d-4cc0-ba20-acfb7d3f1fb1
-- title:
--   Five groups with two scales of pair distances
-- statement:
--   Let \(K,D\) be natural numbers with \(1000(K+1)\le D\), and let \(R\ge3/2\). There are five disjoint groups of \(K\) integer positions. For every positive cross-group distance \(d\), one of \(s=D\) and \(s=DR\) satisfies \(0.999s\le d\le2.668s\) if \(R<5/2\), or \(0.899s\le d\le2.101s\) if \(R\ge5/2\).
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Banks–Freiberg–Maynard, https://arxiv.org/abs/1404.5094. Polymath, https://arxiv.org/abs/1407.4897.

import Mathlib

theorem Erdos287.five_groups_with_two_scale_distance_bands (K D : ℕ) (hD : 1000 * (K + 1) ≤ D)
    (R : ℝ) (hR : (3 / 2 : ℝ) ≤ R) :
    ∃ z : Fin 5 × Fin K → ℕ, Function.Injective z ∧
      ∀ i j, i.1 ≠ j.1 → z i < z j → ∃ s : ℝ, (s = D ∨ s = D * R) ∧
        if R < 5 / 2 then
          (999 / 1000 : ℝ) * s ≤ (z j : ℝ) - z i ∧
            (2668 / 1000 : ℝ) * s ≥ (z j : ℝ) - z i
        else
          (899 / 1000 : ℝ) * s ≤ (z j : ℝ) - z i ∧
            (2101 / 1000 : ℝ) * s ≥ (z j : ℝ) - z i := by sorry
