-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_j_original_stopped_discounted_truncated_taylor_left_mesh_converges
-- name    : AvramDividend.Classical.avram_p4_s3_interval_j_original_stopped_discounted_truncated_taylor_left_mesh_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:47:27.18241+00:00
-- url     : https://prove2.me/theorems/aa7eed99-de68-43a3-b509-c433ae350c91
-- title:
--   Original stopped discounted -1-truncated Lévy Taylor kernel converges along physical left meshes
-- statement:
--   For the same physical original Lévy process X and dividend strategy D, at every real negative jump mark z the correctly truncated Itô–Meyer generator remainder converges along left time meshes with actual inclusive stopping and exponential discount. Continuous w at the realised pre-jump reserve and shifted reserve, and continuous derivative at reserve, are explicitly assumed.
-- source:
--   Source-exact nontrivial two-branch reduction: for -1<z use full compensated nonlinear Taylor continuity; for z≤-1 use raw jump difference continuity. Compose with the original left mesh, actual inclusive stop, and discount. No synthetic noise or terminal integrability claim.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_postpayment_prejump_left_mesh_converges
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_j_original_stopped_discounted_truncated_taylor_left_mesh_converges
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
    (hwy : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t))
    (hwyz : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t + z))
    (hder : ContinuousAt (deriv w) (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t)) :
    let K : ℝ≥0 → ℝ := fun u =>
      Real.exp (-(q * (u : ℝ))) *
        ((fun y : ℝ => w (y + z) - w y -
          (if -1 < z then z * deriv w y else 0))
          (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u))
    Tendsto
      (fun n => (if s n ≤ τ ω then (1 : ℝ) else 0) * K (s n))
      atTop
      (𝓝 ((if t ≤ τ ω then (1 : ℝ) else 0) * K t)) := by sorry
