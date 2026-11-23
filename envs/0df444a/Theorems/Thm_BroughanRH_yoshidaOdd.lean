-- Prove2me | Theorems.Thm_BroughanRH_yoshidaOdd
-- name    : BroughanRH.yoshidaOdd
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:27:49.305643+00:00
-- url     : https://prove2.me/theorems/060f3e06-b8e7-4581-8e67-d4fc6c9524db
-- title:
--   Yoshida’s positivity on odd tests
-- statement:
--   The Weil quadratic form is nonnegative on every odd smooth, compactly supported complex test function. [Source](https://prove2.me/theorems/22770c57-ee68-4a0c-96e7-e0ef164a79f9).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 11.3. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

namespace BroughanRH

theorem yoshidaOdd :
    ∀ f : ℝ → ℂ, ConnesRZ.IsTest f → (∀ x : ℝ, f (-x) = -f x) → 0 ≤ (ConnesRZ.weilDistribution (ConnesRZ.conv f (ConnesRZ.starInv f))).re := by sorry

end BroughanRH
