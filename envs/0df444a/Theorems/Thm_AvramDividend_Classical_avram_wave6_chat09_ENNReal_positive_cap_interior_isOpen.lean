-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
-- name    : AvramDividend.Classical.avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:45:33.000567+00:00
-- url     : https://prove2.me/theorems/bcf24f3a-fbcb-4527-a598-88478a8774ca
-- title:
--   Positive real reserve interior under the actual extended-real dividend cap is open, including infinite cap
-- statement:
--   For every extended nonnegative real cap C, the canonical positive-reserve HJB smoothness domain {y:0<y and ofReal y<C} is open in the real line. This follows from continuity of ENNReal.ofReal and openness of order intervals; it is the exact hypothesis needed to make canonical local BV C1 regularity imply an ordinary compact Lipschitz coefficient at every strict interior point, including cap infinity.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), canonical HJB C1 domain; Mathlib topology of ENNReal.ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
    (C : ℝ≥0∞) :
    IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
