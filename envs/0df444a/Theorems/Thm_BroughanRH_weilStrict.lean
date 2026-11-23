-- Prove2me | Theorems.Thm_BroughanRH_weilStrict
-- name    : BroughanRH.weilStrict
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:26:09.6895+00:00
-- url     : https://prove2.me/theorems/e102bc21-18f6-49b3-b5d6-9bf58a26a765
-- title:
--   Strict Weil positivity for nonzero tests
-- statement:
--   Weil’s form is strictly positive on every nonzero smooth compactly supported test. Logarithmic coordinates with the half-density factor identify this with the multiplicative formulation in Theorem 9.6.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 9.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

namespace BroughanRH

theorem weilStrict :
    ∀ f : ℝ → ℂ, ConnesRZ.IsTest f → f ≠ 0 → 0 < (ConnesRZ.weilDistribution (ConnesRZ.conv f (ConnesRZ.starInv f))).re := by sorry

end BroughanRH
