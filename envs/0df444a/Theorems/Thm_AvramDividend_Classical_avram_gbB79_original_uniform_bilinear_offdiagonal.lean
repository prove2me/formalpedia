-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB79_original_uniform_bilinear_offdiagonal
-- name    : AvramDividend.Classical.avram_gbB79_original_uniform_bilinear_offdiagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:11:56.219177+00:00
-- url     : https://prove2.me/theorems/6c957073-d4c8-40f0-9be0-1bf3484b4761
-- title:
--   Original uniform grid bilinear predictable orthogonality across distinct cells
-- statement:
--   Prove bilinear orthogonality for two bounded adapted original Gaussian predictable coefficient fields, cancelling off-diagonal terms using disjoint original-process increments and their L2 integrability.
-- source:
--   Direct children of published gbB77, upstream gbB76 original two-grid covariance

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB79_original_uniform_bilinear_offdiagonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (H J : ℕ → Ω → ℝ)
    (hHAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (H i))
    (hJAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (J i))
    (hHBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |H i ω| ≤ B)
    (hJBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |J i ω| ≤ B) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Z : ℕ → Ω → ℝ := fun i ω => X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    (∫ ω, ((Finset.range N).sum (fun i => H i ω * Z i ω)) * ((Finset.range N).sum (fun i => J i ω * Z i ω)) ∂P) =
      (Finset.range N).sum (fun i => ∫ ω, (H i ω * Z i ω) * (J i ω * Z i ω) ∂P) := by sorry
