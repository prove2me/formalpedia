-- Prove2me | Theorems.Thm_AvramDividend_Classical_two_sided_exit_stopped_scale_identity
-- name    : AvramDividend.Classical.two_sided_exit_stopped_scale_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T18:57:20.675419+00:00
-- url     : https://prove2.me/theorems/09663d0d-c23e-47da-b5b9-1bbf28449a4d
-- title:
--   Stopped q-scale martingale identity for two-sided exit
-- statement:
--   For 0≤x≤a, stop the killed q-scale martingale e^{-qt}W(x+X_t) at the first upward passage of a or the first downward passage below zero. On downward exit, W vanishes because it is zero on negative arguments. On successful upward exit, spectral negativity prevents positive overshoot, so the stopped scale value is W(a). Optional stopping therefore gives W(x) as the killed upward-exit discount factor multiplied by W(a). This theorem isolates precisely the stochastic optional-stopping content of the two-sided exit identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), equation (3.6), expressed as the stopped q-scale martingale identity before division by W(a).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.two_sided_exit_stopped_scale_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by sorry
