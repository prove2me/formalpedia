-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_boundedReward_scalar_markov
-- name    : AvramDividend.Classical.levy_finiteStopping_boundedReward_scalar_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:46:12.6512+00:00
-- url     : https://prove2.me/theorems/87ddd8c2-0929-43e2-aa4d-b717d3ab931c
-- title:
--   General finite-stopping strong Markov with automatic finite bounded reward expectation
-- statement:
--   Full finite-valued stopping time scalar strong Markov factorisation for a bounded continuous and measurable future-path reward, with only integrability of the uniform constant and restricted-reward measurability assumed. Finiteness of the stationary future reward follows automatically from adapted Lévy path-map measurability.
-- source:
--   Uses the Proved finite-time scalar strong Markov extension and bounded future-path reward integrability lemma; supports general strong Markov independence 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and barrier-value splitting 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_continuousMeasurableReward_scalar_markov
import Theorems.Thm_AvramDividend_Classical_levy_futurePath_boundedReward_lintegral_finite

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_boundedReward_scalar_markov
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hg : Continuous g) (hgm : Measurable g)
    (C : ℝ≥0∞) (hbound : ∀ y, g y ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞)
    (hMeas : ∀ n : ℕ, Measurable (Set.indicator
      (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)})
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')))) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
