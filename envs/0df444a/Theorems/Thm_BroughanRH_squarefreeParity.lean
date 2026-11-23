-- Prove2me | Theorems.Thm_BroughanRH_squarefreeParity
-- name    : BroughanRH.squarefreeParity
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:11:35.054819+00:00
-- url     : https://prove2.me/theorems/4d200ecf-b948-48a8-9c96-49c0d9dc13e1
-- title:
--   Parity among squarefree integers
-- statement:
--   The absolute difference between the counts of positive squarefree integers through $N$ with an even and an odd number of prime factors is $O_\varepsilon(N^{1/2+\varepsilon})$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Cor. 4.17. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem squarefreeParity :
    let pos (N : ℕ) := (Finset.Icc 1 N).filter fun n => Squarefree n ∧ Even n.primeFactors.card
    let neg (N : ℕ) := (Finset.Icc 1 N).filter fun n => Squarefree n ∧ Odd n.primeFactors.card
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => |((pos N).card : ℝ) - ((neg N).card : ℝ)|) (fun N : ℕ => (N : ℝ)^(1/2+ε)) := by sorry

end BroughanRH
