-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps12_original_cap_C2_inclusive_fixed_mark_Taylor_mesh
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps12_original_cap_C2_inclusive_fixed_mark_Taylor_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:19:28.973062+00:00
-- url     : https://prove2.me/theorems/55110b98-772f-4e73-b5e6-68b98dd30786
-- title:
--   Actual stopped Lévy Taylor fixed-mark mesh convergence from canonical capped C2 and zero boundary
-- statement:
--   For Avram original X/D and genuine inclusive stopping time, canonical C2 smoothness on ENNReal cap, the zero-extended candidate with w(0)=0, and an interior pre-jump state imply the full fixed-mark discounted Taylor left-mesh convergence. Crucially handles w(Y+z) at negative reserve or the origin without assuming its continuity; w(0)=0 supplies it. No global jump-integral convergence is claimed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_stopped_discounted_fixed_mark_taylor_left_mesh_converges
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps11_original_ennreal_cap_C2_to_real_band
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_zero_extended_value_continuous

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps12_original_cap_C2_inclusive_fixed_mark_Taylor_mesh
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
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0) (hwzero : w 0 = 0)
    (hy : Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t ∈ Ioo (0 : ℝ) c) :
    let K : ℝ≥0 → ℝ := fun u =>
      Real.exp (-(q * (u : ℝ))) *
        ((fun y : ℝ => w (y + z) - w y - z * deriv w y)
          (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u))
    Tendsto
      (fun n => (if s n ≤ τ ω then (1 : ℝ) else 0) * K (s n))
      atTop
      (𝓝 ((if t ≤ τ ω then (1 : ℝ) else 0) * K t)) := by sorry
