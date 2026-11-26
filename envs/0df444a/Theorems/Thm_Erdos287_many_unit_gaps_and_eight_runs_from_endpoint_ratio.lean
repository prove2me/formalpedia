-- Prove2me | Theorems.Thm_Erdos287_many_unit_gaps_and_eight_runs_from_endpoint_ratio
-- name    : Erdos287.many_unit_gaps_and_eight_runs_from_endpoint_ratio
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:21:21.444246+00:00
-- url     : https://prove2.me/theorems/e5d0c792-3c1a-407d-988f-2cde504b689f
-- title:
--   Many unit gaps and length-eight runs from the endpoint ratio
-- statement:
--   Suppose $m=n_0\ge3000$ and $M=n_{k-1}$ are the first and last denominators of a strictly increasing unit-fraction representation of $1$ with $k\ge2$ and every gap at most two. If $250M\le739m$, there are more than $M/2$ unit gaps and more than $M/100$ starts of runs of eight consecutive selected denominators.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Quantitative gap and run transfer from the endpoint ratio.

import Mathlib

theorem Erdos287.many_unit_gaps_and_eight_runs_from_endpoint_ratio (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ) (hfirst : 3000 ≤ f 0)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hratio : 250 * f (k - 1) ≤ 739 * f 0)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2) :
    let D := (Finset.range k).image f
    let R := (Finset.Icc (f 0) (f (k - 1) + 1 - 8)).filter
      (fun x => ∀ i ∈ Finset.range 8, x + i ∈ D)
    let U := (Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)
    f (k - 1) < 2 * U.card ∧ f (k - 1) < 100 * R.card := by sorry
