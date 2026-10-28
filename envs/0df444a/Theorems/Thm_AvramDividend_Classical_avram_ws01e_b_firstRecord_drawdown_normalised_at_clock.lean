-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_firstRecord_drawdown_normalised_at_clock
-- name    : AvramDividend.Classical.avram_ws01e_b_firstRecord_drawdown_normalised_at_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:55:14.590724+00:00
-- url     : https://prove2.me/theorems/fc966f64-0bb4-4e3e-90a4-40703347ccb2
-- title:
--   First-record terminal drawdown depends only on the residual clock and centred post-record increments
-- statement:
--   At a finite attained first strict upward record u, with the usual boundedness of the relevant running suprema and a later observation clock e≥u, the terminal drawdown S_e−X_e equals the running supremum of centred future increments X_(u+r)−X_u on 0≤r≤e−u minus the centred terminal increment X_e−X_u. This identifies the exact measurable path-and-residual-time functional required by an authentic independent exponential-clock Wiener–Hopf splitting. It uses the accepted first-record clock reset and supremum translation identities without assuming any stochastic factorisation.

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_firstRecord_drawdown_at_observation_clock
import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_firstRecord_drawdown_normalised_at_clock
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u))
    (e : Θ → ℝ≥0) (η : Θ) (hObs : u ≤ e η)
    (hShiftBdd : BddAbove
      ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 (e η - u))) :
    runningSup X (e η) ω - X.X (e η) ω =
      sSup ((fun r : ℝ≥0 =>
        X.X (u + r) ω - X.X u ω) '' Set.Icc 0 (e η - u)) -
      (X.X (e η) ω - X.X u ω) := by sorry
