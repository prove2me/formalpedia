-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb26_original_survival_zero_contact_full_K_exact_discounted_time_integral
-- name    : AvramDividend.Classical.avram_bvb26_original_survival_zero_contact_full_K_exact_discounted_time_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:02:41.529947+00:00
-- url     : https://prove2.me/theorems/57da0020-037b-4343-95f8-4d2fc9e08ca5
-- title:
--   Original physical zero-reserve survivor stopped negative-mark compensator K equals full rate times discounted clipped-time integral
-- statement:
--   On the original bounded-variation finite-activity no-negative-jump linear physical source path, with actual admissible strategy and controlled reserve identically zero through the observation horizon and ruin strictly later, evaluate the actual stopped K compensator defined by the complete original six-guard source marked integrand and original physical time measure mapped from real Lebesgue volume. It equals minus the entire original negative-mark Lévy intensity times boundary value times the discounted physical real-time integral over the exact uniform-grid prefix T-T/(n+2), for each row. This is the missing core source K_n identity required to combine the accepted full-HJB zero-contact compensated cash bound and zero strict-interior generator sum into the original survivor ed067740.
-- source:
--   Original K/H in ed067740; Proved source zero-prepayment and global stop-mark guard e6814efe/ede92794, restricted original full mark integral aa8daed6, original real clock map 24a903f6, discounted prefix limit fb4a3f35.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb26_original_survival_zero_contact_full_K_exact_discounted_time_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_neg : ∀ z < 0, w z = 0)
    (q T : ℝ) (hT : 0 < T) (ω : Ω)
    (S : ℝ≥0) (hS : (S : ℝ) = T)
    (hSource : ∀ t : ℝ≥0, t ≤ S →
       X.X t ω = (t : ℝ) * X.drift)
    (hZero : ∀ t : ℝ≥0, t ≤ S →
       riskProcess X x D t ω = 0)
    (hSurvival : (S : ℝ≥0∞) < ruinTime X x D ω) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → ℝ≥0 → ℝ → ℝ := fun n t z =>
      if 0 < t ∧ (t : ℝ) < T - δ n ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) *
          (w (U t + z) - w (U t)) else 0
    let K : ℕ → ℝ := fun n =>
      ∫ t, ∫ z, H n t z ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∀ n : ℕ,
      K n = -(w 0 * (X.ν (Iio (0 : ℝ))).toReal) *
        (∫ t in Ioc (0 : ℝ) (T - δ n),
          Real.exp (-(q * t)) ∂(volume : Measure ℝ)) := by sorry
