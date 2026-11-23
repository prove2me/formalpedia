-- Prove2me | Theorems.Thm_BroughanRH_sekatskii
-- name    : BroughanRH.sekatskii
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:24:33.334012+00:00
-- url     : https://prove2.me/theorems/268f19df-d555-40ee-be99-d9eeba06845c
-- title:
--   Sekatskii’s shifted positivity sums
-- statement:
--   For each real shift $a<1/2$ and positive integer $n$, Sekatskii’s shifted sum over the nontrivial zeros is nonnegative, counting multiplicity.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §4.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

namespace BroughanRH

theorem sekatskii :
    let Z := {s : ℂ // ConnesRZ.IsCriticalZero s}
    ∀ a : ℝ, a < 1/2 → ∀ n : ℕ, 0 < n →
      let u (ρ : Z) : ℝ := (ConnesRZ.zeroMult ρ.val : ℝ) * (1 - ((ρ.val - (a : ℂ)) / (ρ.val + (a : ℂ)-1))^n).re
      Summable u ∧ 0 ≤ ∑' ρ : Z, u ρ := by sorry

end BroughanRH
