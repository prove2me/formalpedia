-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux13_original_jump_cutoff_transform_tendsto
-- name    : AvramDividend.Classical.avram_redux13_original_jump_cutoff_transform_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:38:54.446407+00:00
-- url     : https://prove2.me/theorems/a3c4a786-f196-4ae8-8b0f-320243961770
-- title:
--   Original BV actual negative-jump exponential transforms converge as cutoffs vanish
-- statement:
--   The original bounded-variation Lévy process has, at each integer horizon, an actual negative-jump Laplace expectation that is the limit of the expectations of its finite-cutoff negative-jump sums. The cutoff is strictly greater than 1/(k+1). The proof must establish pathwise convergence of authentic jump sums and dominated convergence of the bounded exponentials.
-- source:
--   Faithful source-path stochastic half of the corrected Redux12b limit theorem; relies on BV total jump variation and actual original-path left jumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_redux13_original_jump_cutoff_transform_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ n : ℕ,
            Tendsto (fun k : ℕ =>
        (∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P)) atTop (𝓝
        ((∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P))) := by sorry
