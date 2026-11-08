-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian19_original_physical_clock_gradient_L2_sequence
-- name    : AvramDividend.Classical.avram_ubv_gaussian19_original_physical_clock_gradient_L2_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:04:29.746578+00:00
-- url     : https://prove2.me/theorems/272fdce2-7d8b-4e27-9954-f9aa7896e594
-- title:
--   Construct original Gaussian gradient elementary L² approximants under the actual finite physical time-probability measure
-- statement:
--   For each original Avram filtration and finite horizon T, choose a finite measure on its right-continuous predictable sigma algebra that agrees with the actual physical Lebesgue-on-[0,T] times P measure on every predictable set. Under this physical measure, the original prepayment gradient admits an L² convergent sequence of finite linear combinations of original adapted rectangle indicators. It fixes the measure as the genuine physical clock, retaining original process and dividend dynamics.
-- source:
--   Combine Proved e73b5fba original finite physical predictable measure with Proved 3b348621 original gradient elementary L² sequence; bridge for the physical Gaussian simple-gain isometry feeding fdb9a6a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_trimmed_physical_clock_exists
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian18_original_gradient_elementary_L2_sequence

open MeasureTheory Set Filter TopologicalSpace AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian19_original_physical_clock_gradient_L2_sequence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) :
    ∃ (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)),
      ∃ (hfinite : μ Set.univ < ⊤),
      (∀ A : Set (ℝ≥0 × Ω), MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A) ∧
      (letI : IsFiniteMeasure μ := ⟨hfinite⟩
       let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
         (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let G : ℝ≥0 × Ω → ℝ := fun p =>
         X.σ * (if Y p ∈ Icc u v then deriv w (Y p) else 0)
       let Tset : Set (Set (ℝ≥0 × Ω)) :=
         {A | (∃ B : Set Ω, MeasurableSet[𝓕.rightCont 0] B ∧
                    A = ({0} ×ˢ B)) ∨
              (∃ t : ℝ≥0, ∃ B : Set Ω, MeasurableSet[𝓕.rightCont t] B ∧
                    A = (Ioi t ×ˢ B))}
       let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
         {z | ∃ (A : Set (ℝ≥0 × Ω))
             (hA : A ∈ insert univ (insert ∅ Tset))
             (hm : MeasurableSet[𝓕.rightCont.predictable] A)
             (hfin : μ A ≠ ⊤),
             indicatorConstLp (2 : ℝ≥0∞) hm hfin (1 : ℝ) = z}
       ∃ e : ℕ → Lp ℝ (2 : ℝ≥0∞) μ,
         (∀ n, e n ∈ Submodule.span ℝ S) ∧
         Tendsto e atTop (𝓝 ((avram_ubv_gaussian17_original_masked_gradient_MemLp
           X x D hD w a b u v hw hau huv hvb μ hfinite).toLp G))) := by sorry
