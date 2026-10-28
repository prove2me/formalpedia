-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_shifted_drawdown_survival_iff
-- name    : AvramDividend.Classical.firstRecord_shifted_drawdown_survival_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:02:43.305906+00:00
-- url     : https://prove2.me/theorems/e8b117ec-e17e-47bf-9150-dff2c997f433
-- title:
--   Future reflected survival after a record is equivalent to shifted-path drawdown survival
-- statement:
--   Fix any finite attained first strict record u of level b≥0. Over a future horizon T, the original reflected drawdown remains at most a at all times u+t for t≤T exactly when the drawdown of the shifted future raw path remains at most a at all t≤T. This event-level equivalence makes the post-record survival indicator a reward measurable from the future increment path and supports first-record killed renewal under strong Markov.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, reflected-barrier survival restart at record times.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstRecord_drawdown_post_shift_reset

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.firstRecord_shifted_drawdown_survival_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u))
    (a : ℝ) (T : ℝ≥0) :
    (∀ t : ℝ≥0, t ≤ T → reflectedSup X (u + t) ω ≤ a) ↔
      (∀ t : ℝ≥0, t ≤ T →
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
          X.X (u + t) ω ≤ a) := by sorry
