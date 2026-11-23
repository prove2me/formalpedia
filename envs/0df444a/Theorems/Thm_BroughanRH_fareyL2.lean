-- Prove2me | Theorems.Thm_BroughanRH_fareyL2
-- name    : BroughanRH.fareyL2
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:20:21.299854+00:00
-- url     : https://prove2.me/theorems/de1af4d9-294e-430d-9cb3-741c87b35924
-- title:
--   Franel’s squared Farey discrepancy
-- statement:
--   The positive Farey fractions through denominator $N$ are compared with their increasing ranks divided by their total count. Sum the squared discrepancies to obtain growth $O_\varepsilon(N^{-1+\varepsilon})$. [Source](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/farey.pdf).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I §10.3. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem fareyL2 :
    let F (N : ℕ) : Finset ℚ := (Finset.Icc 1 N).biUnion fun q =>
      ((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a : ℕ => (a : ℚ) / q
    let D (N : ℕ) (r : ℚ) : ℝ := (r : ℝ) - (((F N).filter (fun u => u ≤ r)).card : ℝ) / (F N).card
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun N : ℕ => ∑ r ∈ F N, (D N r)^2) (fun N : ℕ => (N : ℝ)^(-1 + ε)) := by sorry

end BroughanRH
