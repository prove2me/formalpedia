-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
-- name    : AvramDividend.Classical.avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:14:19.28177+00:00
-- url     : https://prove2.me/theorems/900bfbce-d300-4373-ba5c-20fd67b5f288
-- title:
--   Original finite negative Lévy activity: physical-jump exponential equals a finite marked product on one conull event
-- statement:
--   On the original spectrally negative Lévy filtered probability space with finite total negative mark intensity, the exponential of the true causal physical jump sum agrees almost surely with a finite product over precisely the nonzero physical jump times, for every fixed horizon and real tilt. The Gaussian component is unrestricted.
-- source:
--   Already Proved A66 actual finiteactivity cumulative negative jump support; A35 finite-support causal tsum equality; A53 elementary finite marked exponential product identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0) :
    ∀ᵐ ω ∂P,
      ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧
        Real.exp (θ * J ω) =
          ∏ u ∈ S, if u ≤ t then
            Real.exp (θ * (X.X u ω -
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u))
          else 1 := by sorry
