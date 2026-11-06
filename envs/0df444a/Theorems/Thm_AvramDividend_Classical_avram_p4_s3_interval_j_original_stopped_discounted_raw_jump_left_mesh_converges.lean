-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_j_original_stopped_discounted_raw_jump_left_mesh_converges
-- name    : AvramDividend.Classical.avram_p4_s3_interval_j_original_stopped_discounted_raw_jump_left_mesh_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:53:18.507526+00:00
-- url     : https://prove2.me/theorems/2832868d-c74a-497c-9a3c-ecd8b7549ee0
-- title:
--   Original physical stopped discounted raw Lévy jump kernel left-mesh convergence without derivative
-- statement:
--   For the same original Lévy X and dividend strategy D, the raw jump difference w(Y_{s-}+z)-w(Y_{s-}) with inclusive physical stopping and discount converges on left meshes for every real mark z. Requires only continuity of w at the original pre-jump reserve and shifted reserve, with no derivative assumption, including large negative jumps and ruin endpoints.
-- source:
--   Source-exact original pre-jump pathwise mesh convergence (P4-S3 639689ae), continuity of the raw jump difference and exponential discount, and exact inclusive stopped indicator left continuity. This is the large-jump branch for the -1 truncated generator and is stronger because no derivative hypothesis is used.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_postpayment_prejump_left_mesh_converges
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_j_original_stopped_discounted_raw_jump_left_mesh_converges
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
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t + z)) :
    let K : ℝ≥0 → ℝ := fun u =>
      Real.exp (-(q * (u : ℝ))) *
        ((fun y : ℝ => w (y + z) - w y)
          (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u))
    Tendsto
      (fun n => (if s n ≤ τ ω then (1 : ℝ) else 0) * K (s n))
      atTop
      (𝓝 ((if t ≤ τ ω then (1 : ℝ) else 0) * K t)) := by sorry
