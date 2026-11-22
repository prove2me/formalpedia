-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_reciprocal_physical_compensated_Lp2_limit_exists
-- name    : AvramDividend.Classical.avram_twoagentA_original_allnu_reciprocal_physical_compensated_Lp2_limit_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:41:41.495308+00:00
-- url     : https://prove2.me/theorems/e78dfd11-3df0-4996-9d90-e9808a7fcf45
-- title:
--   True original infinite-activity compensated negative-mark physical Lévy jump Lp2 limit exists
-- statement:
--   From actual original-X marked jump counts and compensating original ν, construct an explicit sequence of Lp(Ω,2) representatives of each physical finite reciprocal jump partial sum and prove it converges in L2. Use publicly proved finite-band MemLp2, newly proved uniform pairwise expected squared tail Cauchy, and real squared energy to L2 eLpNorm Cauchy. Includes arbitrary negative Lévy activity and Gaussian σ with no synthetic Poisson replacement. Represents the actual original stochastic compensated small-mark integral at fixed T as the Lp2 limit of physical sums.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_anyactivity_physical_reciprocal_finite_annulus_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_anyactivity_physical_reciprocal_partial_sums_L2_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian15_real_squared_energy_to_L2_cauchy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_original_allnu_reciprocal_physical_compensated_Lp2_limit_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let F : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range n,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    ∃ M : ℕ → Lp ℝ 2 P,
      (∀ n, (M n : Ω → ℝ) =ᵐ[P] F n) ∧
        ∃ L : Lp ℝ 2 P, Tendsto M atTop (𝓝 L) := by sorry
