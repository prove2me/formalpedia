-- Prove2me | Theorems.Thm_BroughanRH_bombieri
-- name    : BroughanRH.bombieri
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:26:22.892523+00:00
-- url     : https://prove2.me/theorems/be1486e2-56a8-460f-8bdd-c74c4ae96c02
-- title:
--   Bombieri’s positive variational lower bound
-- statement:
--   For each fixed compact support interval in logarithmic coordinates, the Rayleigh quotient of the Weil form on nonzero smooth tests has a strictly positive infimum. Compact finite unions are contained in an interval. Extending from the smooth core to the form domain uses the density argument of §9.7.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 9.11. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

namespace BroughanRH

theorem bombieri :
    ∀ a : ℝ, 0 < a → ∃ c : ℝ, 0 < c ∧
      ∀ f : ℝ → ℂ, ConnesRZ.IsTest f → tsupport f ⊆ Set.Icc (-a) a →
        c * (∫ x : ℝ, ‖f x‖^2) ≤ (ConnesRZ.weilDistribution (ConnesRZ.conv f (ConnesRZ.starInv f))).re := by sorry

end BroughanRH
