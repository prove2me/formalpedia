-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger67_original_clipped_gaussian_mesh_stops_measurable
-- name    : AvramDividend.Classical.avram_gledger67_original_clipped_gaussian_mesh_stops_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:11:15.932679+00:00
-- url     : https://prove2.me/theorems/934bd107-9ecf-4730-bfdc-097e42768dea
-- title:
--   Original clipped physical Gaussian mesh times are measurable bounded stopping times
-- statement:
--   Every deterministic physical mesh time clipped at the same original rho is a bounded stopping time of the original right-continuous filtration, and its WithTop-valued clock is measurable. All random cell endpoints retain the original finite horizon bound.
-- source:
--   Necessary exact stopped-observable interface for gledger53 original physical source positive L1 and gledger62 original stopped exponential moment application.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger67_original_clipped_gaussian_mesh_stops_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (n m : ℕ) (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    ∀ i : ℕ,
      IsStoppingTime 𝓕.rightCont (fun ω =>
        min (ρ ω : WithTop ℝ≥0) ((i : ℝ≥0) * Δ)) ∧
      Measurable (fun ω =>
        min (ρ ω : WithTop ℝ≥0) ((i : ℝ≥0) * Δ)) ∧
      (∀ ω, min ((i : ℝ≥0) * Δ) (ρ ω) ≤ (n : ℝ≥0)) := by sorry
