-- Prove2me | Theorems.Thm_BroughanRH_fareyL1
-- name    : BroughanRH.fareyL1
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:19:19.954799+00:00
-- url     : https://prove2.me/theorems/28365fad-9e84-43d3-bda2-edcddc353b4a
-- title:
--   Landau’s absolute Farey discrepancy
-- statement:
--   The positive Farey fractions through denominator $N$ are compared with their increasing ranks divided by their total count. Sum the absolute discrepancies to obtain growth $O_\varepsilon(N^{1/2+\varepsilon})$. [Source](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/farey.pdf).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 10.6. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem fareyL1 :
    let F (N : ℕ) : Finset ℚ := (Finset.Icc 1 N).biUnion fun q =>
      ((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a : ℕ => (a : ℚ) / q
    let D (N : ℕ) (r : ℚ) : ℝ := (r : ℝ) - (((F N).filter (fun u => u ≤ r)).card : ℝ) / (F N).card
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun N : ℕ => ∑ r ∈ F N, |D N r|) (fun N : ℕ => (N : ℝ)^(1/2 + ε)) := by sorry

end BroughanRH
