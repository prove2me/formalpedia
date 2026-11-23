-- Prove2me | Theorems.Thm_BroughanRH_liZeroSum
-- name    : BroughanRH.liZeroSum
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:22:33.933427+00:00
-- url     : https://prove2.me/theorems/d0b5d325-f4c3-49b2-81a4-d638a034b67d
-- title:
--   Strict positivity of Li’s sum over zeros
-- statement:
--   The real parts of the positive-index Li summands, counted with zero multiplicity, have a convergent sum strictly greater than zero.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Cor. 4.17 (zero sum). https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

namespace BroughanRH

theorem liZeroSum :
    let Z := {s : ℂ // ConnesRZ.IsCriticalZero s}
    ∀ n : ℕ, 0 < n →
      let u (ρ : Z) : ℝ := (ConnesRZ.zeroMult ρ.val : ℝ) * (1 - (1 - 1/ρ.val)^n).re
      Summable u ∧ 0 < ∑' ρ : Z, u ρ := by sorry

end BroughanRH
