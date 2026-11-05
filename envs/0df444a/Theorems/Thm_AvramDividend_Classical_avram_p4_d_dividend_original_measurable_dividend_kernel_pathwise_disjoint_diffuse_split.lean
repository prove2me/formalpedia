-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_measurable_dividend_kernel_pathwise_disjoint_diffuse_split
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_measurable_dividend_kernel_pathwise_disjoint_diffuse_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:16:16.644286+00:00
-- url     : https://prove2.me/theorems/4b5426a9-293d-44d8-bd50-0c1f67a52665
-- title:
--   Measurable original s-finite dividend kernel with exact pathwise closed-horizon atomic and diffuse restrictions
-- statement:
--   For the original adapted left-continuous dividend strategy, construct the already-proved actual measurable s-finite Stieltjes kernel κ(ω)=dividendMeasure D ω, and for every path and closed horizon exhibit disjoint right-atomic and diffuse restrictions, with the diffuse component dominated by κ(ω). This proves the true source stochastic base kernel and all pathwise measure identities while keeping measurable choice of the random atomic carrier A(ω) as an explicit separate obligation.
-- source:
--   Accepted dividendMeasure_global_sfinite_kernel_exists 766b5129, exact original Stieltjes carrier restrictions 8d308a32 and new source diffuse submeasure domination 72fd52.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_restrict_atoms_diffuse_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_measurable_dividend_kernel_pathwise_disjoint_diffuse_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∃ κ : ProbabilityTheory.Kernel Ω ℝ,
      ProbabilityTheory.IsSFiniteKernel κ ∧
      (∀ ω : Ω, κ ω = dividendMeasure D ω) ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
          A.Countable ∧ MeasurableSet A ∧
          (κ ω).restrict (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse ∧
          ((κ ω).restrict (Icc (0 : ℝ) (T : ℝ))).restrict A = μatom ∧
          ((κ ω).restrict (Icc (0 : ℝ) (T : ℝ))).restrict Aᶜ = μdiffuse ∧
          μdiffuse ≤ κ ω ∧ NullSingletonClass μdiffuse := by sorry
