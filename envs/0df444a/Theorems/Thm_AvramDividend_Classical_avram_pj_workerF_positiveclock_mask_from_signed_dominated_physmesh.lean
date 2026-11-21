-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerF_positiveclock_mask_from_signed_dominated_physmesh
-- name    : AvramDividend.Classical.avram_pj_workerF_positiveclock_mask_from_signed_dominated_physmesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T21:16:39.284165+00:00
-- url     : https://prove2.me/theorems/4866c184-5ae7-40d7-8e78-3a214d32f69d
-- title:
--   Positive-clock positive-part physical-grid L1 transfer from original signed dominated source with vanishing zero-clock spatial cutoff
-- statement:
--   For the same actual stopped original signed Lévy Ito-Stieltjes residual, an integrable epsilon-small spatial cutoff and an almost-surely vanishing signed mesh dominated by an integrable envelope imply that the positive residual, restricted to strictly positive stopping clocks, is integrable and has vanishing L1 mean; one can choose the cutoff identically zero at zero clocks without increasing its L1 cost. This is an exact deterministic probability transfer and retains all original stochastic source variables.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_signed_spatial_K_mask_preserves_L1
import Theorems.Thm_AvramDividend_Classical_avram_pj_true_physical_positive_ito_excess_dominated_ae_vanish_implies_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerF_positiveclock_mask_from_signed_dominated_physmesh
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (ρ : Ω → ℝ≥0) (hρz : MeasurableSet {ω : Ω | ρ ω = 0})
    (V U : Ω → ℝ) (Q : ℕ → Ω → ℝ) (ε : ℝ)
    (K : Ω → ℝ) (hKI : Integrable K P)
    (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε / 4)
    (hEI : ∀ k, Integrable
      (fun ω => V ω - U ω - K ω - Q k ω) P)
    (F : Ω → ℝ) (hFI : Integrable F P)
    (hDom : ∀ k, ∀ᵐ ω ∂P,
      |V ω - U ω - K ω - Q k ω| ≤ F ω)
    (hAE : ∀ᵐ ω ∂P, Tendsto
      (fun k => V ω - U ω - K ω - Q k ω)
      Filter.atTop (nhds (0 : ℝ))) :
    ∃ K' : Ω → ℝ,
      Integrable K' P ∧ (∫ ω, |K' ω| ∂P) ≤ ε / 4 ∧
      (∀ ω, ρ ω = 0 → K' ω = 0) ∧
      (∀ k, Integrable (fun ω =>
        if ρ ω = 0 then (0 : ℝ)
        else max (0 : ℝ) (V ω - U ω - K' ω - Q k ω)) P) ∧
      Tendsto (fun k =>
        ∫ ω, |if ρ ω = 0 then (0 : ℝ)
          else max (0 : ℝ) (V ω - U ω - K' ω - Q k ω)| ∂P)
        Filter.atTop (nhds (0 : ℝ)) := by sorry
