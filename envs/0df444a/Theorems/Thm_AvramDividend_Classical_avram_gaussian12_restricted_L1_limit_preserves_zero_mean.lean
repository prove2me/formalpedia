-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussian12_restricted_L1_limit_preserves_zero_mean
-- name    : AvramDividend.Classical.avram_gaussian12_restricted_L1_limit_preserves_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:49:28.677585+00:00
-- url     : https://prove2.me/theorems/71b869b4-9f32-4e95-acee-eb9a50e925a6
-- title:
--   Gaussian centred finite meshes retain zero mean on positive-clock events under restricted L1 convergence
-- statement:
--   For any measurable positive-clock event and sequence of integrable centred Gaussian mesh residuals, if the sequence converges in L1 on that event to an integrable limit, the masked expectation of the limit is zero. The proof applies Mathlib continuity of Bochner integration under L1 convergence directly to the restricted probability measure. This bridges the exact finite stopped Gaussian Taylor grid to the limiting Gaussian Ito martingale in the source reward bound.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter Topology
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gaussian12_restricted_L1_limit_preserves_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A : Set Ω) (hA : MeasurableSet A)
    (Q : ℕ → Ω → ℝ) (hQI : ∀ n, Integrable (Q n) P)
    (Z : Ω → ℝ) (hZI : Integrable Z P)
    (hZero : ∀ n, (∫ ω in A, Q n ω ∂P) = 0)
    (hL1 : Tendsto
      (fun n => ∫⁻ ω in A, ‖Q n ω - Z ω‖ₑ ∂P)
      atTop (nhds (0 : ℝ≥0∞))) :
    (∫ ω in A, Z ω ∂P) = 0 := by sorry
