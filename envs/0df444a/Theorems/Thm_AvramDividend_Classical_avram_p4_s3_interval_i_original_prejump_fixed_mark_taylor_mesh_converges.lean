-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_prejump_fixed_mark_taylor_mesh_converges
-- name    : AvramDividend.Classical.avram_p4_s3_interval_i_original_prejump_fixed_mark_taylor_mesh_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:07:32.124089+00:00
-- url     : https://prove2.me/theorems/5009822e-be03-4671-be08-7548be867424
-- title:
--   Actual original pre-jump fixed-mark nonlinear Taylor kernel convergence along predictable left meshes
-- statement:
--   For the actual physical controlled reserve of X and dividend D, along any deterministic left-approaching mesh, the true mark-dependent nonlinear Itô–Meyer Taylor kernel w(Y+z)-w(Y)-z deriv w(Y) converges at every fixed physical mark z whenever w is continuous at the two actual limiting reserve values and deriv w is continuous at the limiting reserve. These local regularity conditions are the honest analytic premises supplied on compact C² interior strips, without claiming boundary continuity or uniform L¹/L² dominated convergence.
-- source:
--   First apply the newly Proved original postpayment pre-jump left-mesh convergence (interval-i base helper). Compose continuity of w at Y(t) and Y(t)+z, and continuity of deriv w at Y(t), with the actual sequence Y(s_n) and its translated values. Subtract the two w terms and the derivative linear compensation to obtain the full original nonlinear Taylor kernel convergence at the physical mark z.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_postpayment_prejump_left_mesh_converges
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_i_original_prejump_fixed_mark_taylor_mesh_converges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0)
    (s : ℕ → ℝ≥0) (hsle : ∀ n, s n ≤ t)
    (hst : Tendsto s atTop (𝓝 t))
    (w : ℝ → ℝ) (z : ℝ)
    (hwy : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t))
    (hwyz : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t + z))
    (hder : ContinuousAt (deriv w) (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t)) :
    Tendsto
      (fun n =>
        let y := Function.leftLim
          (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s n)
        w (y + z) - w y - z * deriv w y)
      atTop
      (𝓝 ((fun y : ℝ => w (y + z) - w y - z * deriv w y)
        (Function.leftLim
          (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t))) := by sorry
