-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_deriv_interval_integrable_and_mass_bound
-- name    : AvramDividend.Classical.chat07_scale_deriv_interval_integrable_and_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:09:30.540401+00:00
-- url     : https://prove2.me/theorems/eeecc125-d643-4984-8580-a1bc7308c0ac
-- title:
--   Interval-integrable scale derivative with monotone endpoint mass bound
-- statement:
--   Every real q-scale function is monotone. On any finite real interval its ordinary derivative is interval integrable and the integral lies in the unoriented interval between zero and W(b)-W(a). This follows from the Mathlib monotone derivative integrability and derivative integral mass inequality, without assuming global C1 regularity or local absolute continuity. It supplies the compact-interval derivative measure control needed for the BV weighted compensated Fubini problem.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_deriv_interval_integrable_and_mass_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a b : ℝ) :
    IntervalIntegrable (deriv W) volume a b ∧
      (∫ x in a..b, deriv W x) ∈ uIcc 0 (W b - W a) := by sorry
