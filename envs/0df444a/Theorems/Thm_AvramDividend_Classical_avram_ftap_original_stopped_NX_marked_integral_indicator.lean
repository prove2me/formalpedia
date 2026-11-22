-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_NX_marked_integral_indicator
-- name    : AvramDividend.Classical.avram_ftap_original_stopped_NX_marked_integral_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:17:15.122955+00:00
-- url     : https://prove2.me/theorems/cdf3cf6e-6bc3-4f42-a820-80802725818f
-- title:
--   Actual stopped Lévy marked integrals equal original physical NX clock-masked signed and nonnegative integrals
-- statement:
--   For the original spectrally negative Levy path stopped at any finite random clock, integrals of any real-valued signed mark kernel and any ENNReal-valued nonnegative mark kernel against the actual stopped process's physical time-jump-size counting measure are exactly the corresponding integrals against the original Avram physical marked jump measure NX, with explicit indicator of time at or before the stopping clock. Handles arbitrary negative jump activity and the endpoint jump, and is precisely the two-integral interface for the stopped Ito-Meyer signed residual and compensated positive tail envelope. It follows from already proved exact original marked measure time restriction and the pinned Mathlib signed and lintegral indicator identities. No new stochastic decomposition, artificial martingale, bounded kernel or integrability hypothesis is introduced.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Foundations/Paths.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_NX_time_restrict
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ftap_original_stopped_NX_marked_integral_indicator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (τ : Ω → ℝ≥0) (ω : Ω) :
    (∀ f : (ℝ≥0 × ℝ) → ℝ,
      (∫ p, f p ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
      MeasureTheory.stoppedProcess X.X
          (fun ω => (τ ω : WithTop ℝ≥0)) u ω -
        Function.leftLim
          (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X
            (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        MeasureTheory.stoppedProcess X.X
          (fun ω => (τ ω : WithTop ℝ≥0)) u ω -
          Function.leftLim
            (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X
              (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u)))) =
      (∫ p, ({p : ℝ≥0 × ℝ | p.1 ≤ τ ω}).indicator f p
        ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u))))) ∧
    (∀ g : (ℝ≥0 × ℝ) → ℝ≥0∞,
      (∫⁻ p, g p ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
      MeasureTheory.stoppedProcess X.X
          (fun ω => (τ ω : WithTop ℝ≥0)) u ω -
        Function.leftLim
          (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X
            (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        MeasureTheory.stoppedProcess X.X
          (fun ω => (τ ω : WithTop ℝ≥0)) u ω -
          Function.leftLim
            (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X
              (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u)))) =
      (∫⁻ p, ({p : ℝ≥0 × ℝ | p.1 ≤ τ ω}).indicator g p
        ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u))))) := by sorry
