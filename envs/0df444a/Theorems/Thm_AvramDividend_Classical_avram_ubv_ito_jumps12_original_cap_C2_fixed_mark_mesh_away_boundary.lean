-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps12_original_cap_C2_fixed_mark_mesh_away_boundary
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps12_original_cap_C2_fixed_mark_mesh_away_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:41:03.453613+00:00
-- url     : https://prove2.me/theorems/c803d524-f2fb-485e-ab87-8d29c5c9f289
-- title:
--   Original stopped Lévy Taylor left-mesh convergence away from the zero-reserve contact mark
-- statement:
--   For Avram's exact Lévy path, dividend strategy, stopped clock, and cap-compatible HJB C2 candidate, the discounted Taylor fixed-mark left mesh limit holds at an interior pre-jump state whenever the mark does not land exactly at reserve zero. The boundary value is only assumed continuous from above and zero for negative reserve, and may be positive at the origin. This isolates the exact-contact zero-reserve exceptional mark left for the full Itô-Meyer argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_stopped_discounted_fixed_mark_taylor_left_mesh_converges
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps11_original_ennreal_cap_C2_to_real_band

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps12_original_cap_C2_fixed_mark_mesh_away_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (ω : Ω) (t : ℝ≥0)
    (s : ℕ → ℝ≥0) (hsle : ∀ n, s n ≤ t)
    (hst : Tendsto s atTop (𝓝 t))
    (w : ℝ → ℝ) (q z : ℝ)
    (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hy : Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t ∈ Ioo (0 : ℝ) c)
    (hyz : Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t + z ≠ 0) :
    let K : ℝ≥0 → ℝ := fun u =>
      Real.exp (-(q * (u : ℝ))) *
        ((fun y : ℝ => w (y + z) - w y - z * deriv w y)
          (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u))
    Tendsto
      (fun n => (if s n ≤ τ ω then (1 : ℝ) else 0) * K (s n))
      atTop
      (𝓝 ((if t ≤ τ ω then (1 : ℝ) else 0) * K t)) := by sorry
