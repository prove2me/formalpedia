-- Prove2me | Theorems.Thm_Erdos287_consecutive_runs_from_denominator_density
-- name    : Erdos287.consecutive_runs_from_denominator_density
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:01:26.639603+00:00
-- url     : https://prove2.me/theorems/941a1c8a-d474-5e11-a47f-9104dd85ea34
-- title:
--   Consecutive denominator runs from a density bound
-- statement:
--   Let \(T\subseteq[m,M]\) be a finite set of selected denominators. For \(1\le w\le M+1\), let \(R_w\) be the number of starts of length-\(w\) intervals contained in \(T\). Then \(R_w\ge M+2-m-w-w(M+1-m-|T|)\) whenever \(m\le M\).
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Counting fully selected intervals from denominator density.

import Mathlib

theorem Erdos287.consecutive_runs_from_denominator_density (m M w : ℕ) (_hw : 1 ≤ w) (hwM : w ≤ M + 1)
    (T : Finset ℕ) (hT : T ⊆ Finset.Icc m M) :
    let R := (Finset.Icc m (M + 1 - w)).filter (fun x => ∀ i ∈ Finset.range w, x + i ∈ T)
    M + 2 ≤ m + w + w * (M + 1 - m - T.card) + R.card := by sorry
