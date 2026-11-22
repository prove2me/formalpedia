-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_history_killed_scale_real_ennreal_bridge_no_standing
-- name    : AvramDividend.Classical.p2m81_bv_history_killed_scale_real_ennreal_bridge_no_standing
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T05:10:35.149789+00:00
-- url     : https://prove2.me/theorems/942c4b9b-c13b-4900-a204-1b41ce3aa585
-- title:
--   BV history-killed scale real/ennreal integral bridge from Esscher root without standing (public)
-- statement:
--   For a spectrally negative Levy process with positive discount q, positive Esscher root phi with psi(phi)=q, genuine q-scale function W, and a measurable history survival event to horizon T, the ennreal lintegral of the continuously-killed discounted scale payoff equals the ofReal image of its real integral. No Standing assumption.
-- source:
--   Standing-free replacement for the 6275ef80-shaped bridge step: fixed-time integrability via Proved 0b4c9214, then ofReal_integral_eq_lintegral_ofReal with pointwise indicator congruence. Feeds the scalar identity H1a in the H1 (ee75bf61) decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.p2m81_bv_history_killed_scale_real_ennreal_bridge_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (y : ℝ) (T : ℝ≥0)
    (hMeas : MeasurableSet {z : Ω | ∀ v : ℝ≥0, v ≤ T → 0 ≤ y + X.X v z}) :
    (∫⁻ ω, (if ∀ v : ℝ≥0, v ≤ T → 0 ≤ y + X.X v ω then
        ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (y + X.X T ω))
      else (0 : ℝ≥0∞)) ∂P) =
    ENNReal.ofReal (∫ ω, ({z : Ω | ∀ v : ℝ≥0, v ≤ T → 0 ≤ y + X.X v z}).indicator
        (fun z => Real.exp (-(q * (T : ℝ))) * W (y + X.X T z)) ω ∂P) := by sorry
