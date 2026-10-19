-- Prove2me | Theorems.Thm_AvramDividend_Classical_restrict_Ico_eq_of_local_Ico_mass_eq
-- name    : AvramDividend.Classical.restrict_Ico_eq_of_local_Ico_mass_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T11:38:24.024579+00:00
-- url     : https://prove2.me/theorems/dd16ce16-2a3d-4eff-b3f5-d551882bf5b0
-- title:
--   Equality of locally finite Stieltjes measures on a payment prefix from interval masses
-- statement:
--   Two measures on the real line agree on the restricted half-open interval [0,r) whenever one is locally finite and the two assign equal masses to every subinterval [a,b) with 0≤a≤b≤r. This is proved by uniqueness of locally finite Borel measures on Ico generators, clipping arbitrary generator intervals against [0,r). The bridge permits a dividend-path identity on strict pre-ruin prefixes to become exact Stieltjes payoff-measure equality, including continuous payments.
-- source:
--   Pinned Mathlib Order and MeasureTheory BorelSpace uniqueness theorem, with application to Avram, Palmowski and Pistorius (2007), Section 2, Stieltjes dividends.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.restrict_Ico_eq_of_local_Ico_mass_eq
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ] (r : ℝ)
    (h : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ r →
      μ (Ico a b) = ν (Ico a b)) :
    μ.restrict (Ico 0 r) = ν.restrict (Ico 0 r) := by sorry
