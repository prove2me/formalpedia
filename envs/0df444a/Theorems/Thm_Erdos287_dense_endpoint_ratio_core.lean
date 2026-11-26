-- Prove2me | Theorems.Thm_Erdos287_dense_endpoint_ratio_core
-- name    : Erdos287.dense_endpoint_ratio_core
-- status  : Open
-- author  : @immiq
-- created : 2026-11-26T10:29:49.717945+00:00
-- url     : https://prove2.me/theorems/caca9a18-56c8-56b4-a070-d90193278e14
-- title:
--   Dense endpoint-ratio case of Erdős #287
-- statement:
--   There is no counterexample to Erdős #287 with largest denominator $M>382613443$ and smallest denominator $m$ satisfying $250M\le739m$, with more than $M/2$ unit gaps and more than $M/100$ starts of runs of eight consecutive selected denominators. The count hypotheses follow from the endpoint ratio in this range by https://prove2.me/theorems/e5d0c792-3c1a-407d-988f-2cde504b689f.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.dense_endpoint_ratio_core (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hlarge : 382613443 < f (k - 1))
    (hratio : 250 * f (k - 1) ≤ 739 * f 0)
    (hunit : f (k - 1) < 2 * ((Finset.range (k - 1)).filter
      (fun i => f (i + 1) - f i = 1)).card)
    (hruns :
      let D := (Finset.range k).image f
      let R := (Finset.Icc (f 0) (f (k - 1) + 1 - 8)).filter
        (fun x => ∀ i ∈ Finset.range 8, x + i ∈ D)
      f (k - 1) < 100 * R.card) : False := by sorry
