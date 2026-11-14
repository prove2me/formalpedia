-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb25_original_zero_contact_stopped_K_global_mark_guard_exact
-- name    : AvramDividend.Classical.avram_bvb25_original_zero_contact_stopped_K_global_mark_guard_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:55:34.629195+00:00
-- url     : https://prove2.me/theorems/ede92794-ddba-493f-9cf9-0a819c9a998c
-- title:
--   Original BV zero-contact stopped K marked integrand globally equals source negative boundary loss under physical stop and mark guards
-- statement:
--   On an original physical zero-reserve no-negative-jump path through the finite source horizon, the entire stopped K integrand with the exact six original guards is equal at every physical time and every mark to the negative boundary value times the true discount, retained precisely on positive times within the original uniform clipped prefix, at or before actual ruin, and for genuine negative marks. Outside those time, stopping and mark guards, both integrands are zero. The exact source prepayment U(t) is zero on supported time clocks by the accepted prepayment theorem. This removes U and the artificial zero/cap masks from the actual source stopped time-mark integrand without removing its full negative-mark measure or changing stopping conventions; integration over original source time and negative marks is now the remaining step.
-- source:
--   Accepted exact stopped source K positive-time negative-mark identity e6814efe; original physical K integrand from ed067740 and b0915396; original uniform prefix T-T/(n+2).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb25_original_zero_contact_stopped_K_negative_mark_integrand_exact
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb25_original_zero_contact_stopped_K_global_mark_guard_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ) (hT : 0 < T)
    (S : ℝ≥0) (hS : (S : ℝ) = T)
    (hSource : ∀ s : ℝ≥0, s ≤ S →
      X.X s ω = (s : ℝ) * X.drift)
    (hZero : ∀ s : ℝ≥0, s ≤ S →
      riskProcess X x D s ω = 0)
    (w : ℝ → ℝ) (hw_neg : ∀ z < 0, w z = 0)
    (q : ℝ) (n : ℕ) (t : ℝ≥0) (z : ℝ) :
(if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
          ENNReal.ofReal (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ C ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))
        else 0) =
      (if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧ z < 0 then
        -(Real.exp (-(q * (t : ℝ))) * w 0)
       else 0) := by sorry
