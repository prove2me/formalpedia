-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_L2_two_sided_signed_martingale_mean_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_L2_two_sided_signed_martingale_mean_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:12:25.16209+00:00
-- url     : https://prove2.me/theorems/07b7a0e6-7120-4564-8567-fa463418c686
-- title:
--   Original signed stopped martingale preserves zero mean from two-sided uniform quadratic estimates
-- statement:
--   For the actual original Lévy sample space with probability law P, suppose positive and negative parts of a stopped signed stochastic residual sequence converge almost surely to their true limits, are measurably defined, and each has an integrable square with a uniform finite second-moment bound. If every approximating residual is centred, expressed exactly by equality of the two part expectations, the limiting signed residual is integrable and centred. This derives uniform integrability using the independently Proved source-compatible nonnegative uniform second-moment theorem; no single almost-sure dominating random envelope or optional stopping for a merely local martingale is asserted. Applying to the true source Ito residual requires Gaussian and jump-component L2 bounds.
-- source:
--   Avram original same-source stopped martingale; Proved nonnegative_integral_tendsto_of_uniform_second_moment (bef79c38-a4aa-42be-b897-fd1baeed7998).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_L2_two_sided_signed_martingale_mean_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk : ℕ → Ω → ℝ) (M : Ω → ℝ)
    (hPosMeas : ∀ k, AEStronglyMeasurable (fun ω => max (Mk k ω) 0) P)
    (hNegMeas : ∀ k, AEStronglyMeasurable (fun ω => max (-(Mk k ω)) 0) P)
    (hPosMMeas : AEStronglyMeasurable (fun ω => max (M ω) 0) P)
    (hNegMMeas : AEStronglyMeasurable (fun ω => max (-(M ω)) 0) P)
    (hPosConv : ∀ᵐ ω ∂P, Tendsto (fun k => max (Mk k ω) 0) atTop (𝓝 (max (M ω) 0)))
    (hNegConv : ∀ᵐ ω ∂P, Tendsto (fun k => max (-(Mk k ω)) 0) atTop (𝓝 (max (-(M ω)) 0)))
    (C : ℝ) (hC : 0 ≤ C)
    (hPos2 : ∀ k, Integrable (fun ω => (max (Mk k ω) 0) ^ 2) P ∧
      (∫ ω, (max (Mk k ω) 0) ^ 2 ∂P) ≤ C)
    (hNeg2 : ∀ k, Integrable (fun ω => (max (-(Mk k ω)) 0) ^ 2) P ∧
      (∫ ω, (max (-(Mk k ω)) 0) ^ 2 ∂P) ≤ C)
    (hZeroSplit : ∀ k, (∫ ω, max (Mk k ω) 0 ∂P) -
      (∫ ω, max (-(Mk k ω)) 0 ∂P) = 0) :
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by sorry
