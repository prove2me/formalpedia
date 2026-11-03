-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_controlled_grid_gradient_auto_predictable_L2
-- name    : AvramDividend.Classical.avram_wave7_05_turn4_original_controlled_grid_gradient_auto_predictable_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:58:52.473163+00:00
-- url     : https://prove2.me/theorems/bffcaf64-e95d-4904-991f-dfb50daf7762
-- title:
--   Automatic original-reserve gradient predictable finite-grid exact L2 Gaussian isometry
-- statement:
--   The exact original stopped discounted derivative of x+X.X-rightLimit D is predictable at the deterministic grid starts under the native right-continuous filtration. If ν=0 and its true ruin-masked values are bounded, every disjoint-grid Gaussian gain sum is L2 and obeys exact expected squared-gain finite quadratic-variation isometry, with no additional coefficient-measurability assumptions.
-- source:
--   Proved Wave3 original strong predictability 658fb6a1-1044-40b3-aa7d-2926663389af and source exact variance/isometry f3ae0c12-e779-4f7a-af92-e004499196c7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_controlled_grid_gradient_exact_L2_isometry

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn4_original_controlled_grid_gradient_auto_predictable_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ i ∈ S, ∀ ω : Ω,
      |(if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0)| ≤ K) :
    let G : ι → Ω → ℝ := fun i ω =>
      if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by sorry
