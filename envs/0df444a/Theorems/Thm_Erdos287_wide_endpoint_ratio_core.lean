-- Prove2me | Theorems.Thm_Erdos287_wide_endpoint_ratio_core
-- name    : Erdos287.wide_endpoint_ratio_core
-- status  : Open
-- author  : @immiq
-- created : 2026-11-26T10:29:49.229358+00:00
-- url     : https://prove2.me/theorems/893e48ae-aa13-4fc6-84ec-018554c008d4
-- title:
--   Wide endpoint-ratio case of Erdős #287
-- statement:
--   A counterexample to Erdős #287 with largest denominator $M>382613443$ cannot have $250M>739m$, where $m$ is the first denominator. The affine Chen argument at https://prove2.me/theorems/924ec7e1-390d-5545-8c15-732932b0a79a gives an asymptotic exclusion. This target also requires handling the range below its threshold.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.wide_endpoint_ratio_core (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hlarge : 382613443 < f (k - 1))
    (hwide : 739 * f 0 < 250 * f (k - 1)) : False := by sorry
