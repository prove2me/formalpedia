-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_continuousCylinderReward_scalar_markov
-- name    : AvramDividend.Classical.levy_finiteStopping_continuousCylinderReward_scalar_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:07:18.647929+00:00
-- url     : https://prove2.me/theorems/4970db42-792d-486d-93d3-0bc0d26c624f
-- title:
--   Finite-stopping strong Markov factorisation for continuous finite-dimensional rewards
-- statement:
--   The strong Markov factorisation for any finite stopping time holds for bounded continuous measurable rewards of finitely many future increments of a Lévy process, on a stopped-history event. The measurable truncated reward premise is explicit and can be discharged separately from càdlàg path measurability.
-- source:
--   Specialises Proved finite-stopping bounded future-path reward formula to arbitrary finite coordinate sets. A finite-dimensional law bridge toward the whole stopped Lévy path factorisation 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and barrier splitting 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_boundedReward_scalar_markov

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_continuousCylinderReward_scalar_markov
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (J : Finset ℝ≥0)
    (h : (J → ℝ) → ℝ≥0∞)
    (hh : Continuous h) (hhm : Measurable h)
    (C : ℝ≥0∞) (hbound : ∀ z, h z ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞)
    (hMeas : ∀ n : ℕ, Measurable (Set.indicator
      (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)})
      (fun ω' : Ω => h (fun j : J =>
        X.X (τ ω' + (j : ℝ≥0)) ω' - X.X (τ ω') ω')))) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => h (fun j : J =>
        X.X (τ ω' + (j : ℝ≥0)) ω' - X.X (τ ω') ω')) ω ∂P) =
      P A * (∫⁻ y, h (fun j : J => y (j : ℝ≥0))
        ∂(Measure.map
          (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
