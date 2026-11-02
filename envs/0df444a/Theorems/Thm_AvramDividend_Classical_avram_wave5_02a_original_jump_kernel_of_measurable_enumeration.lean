-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_jump_kernel_of_measurable_enumeration
-- name    : AvramDividend.Classical.avram_wave5_02a_original_jump_kernel_of_measurable_enumeration
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:30:54.78249+00:00
-- url     : https://prove2.me/theorems/119a5d3f-c927-4d10-9468-6912d9db7404
-- title:
--   Actual original jump measure admits an s-finite kernel from measurable jump enumeration
-- statement:
--   If measurable active domains and measurable marked selectors enumerate exactly the literal original intrinsic jump measure as a sum of Dirac masses, construct an s-finite kernel equal to that original measure at every sample. The existence of this faithful measurable enumeration is an explicit separate obligation.
-- source:
--   Countable sums of piecewise deterministic finite kernels and the given exact original jump measure enumeration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_original_jump_kernel_of_measurable_enumeration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (f : ℕ → Ω → (ℝ≥0 × ℝ)) (hf : ∀ n, Measurable (f n))
    (hEnum : ∀ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
      Measure.sum (fun n => (A n).indicator (fun _ => Measure.dirac (f n ω)) ω)) :
    ∃ κ : Kernel Ω (ℝ≥0 × ℝ), IsSFiniteKernel κ ∧
      ∀ ω, κ ω =
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by sorry
