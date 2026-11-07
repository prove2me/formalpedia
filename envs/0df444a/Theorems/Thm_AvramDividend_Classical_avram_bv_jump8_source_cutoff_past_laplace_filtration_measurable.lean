-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_source_cutoff_past_laplace_filtration_measurable
-- name    : AvramDividend.Classical.avram_bv_jump8_source_cutoff_past_laplace_filtration_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T18:02:28.876228+00:00
-- url     : https://prove2.me/theorems/154a6ab1-7fb7-4e1d-a223-ceaf5d0e8451
-- title:
--   Original intrinsic cutoff marked-jump Laplace past weight is measurable at its own filtration horizon
-- statement:
--   For any integer n, strict negative jump-size cutoff k and actual original spectrally negative Lévy process, the nonlinear cutoff marked-jump exponential on (0,n] is measurable relative to source filtration 𝓕_n. Derive from adaptedness, càdlàg countable extraction of intrinsic jump marks, and cutoff approximations; this does not assume arbitrary PRM independence.
-- source:
--   Use X.adapted, X.rightCont, X.leftLim and Proved finite marked-time extraction facts. After proving this child, Proved deterministic-time product law cd9853a4 plus measurable shifted path version b879a7 yield original nonlinear Laplace independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_source_cutoff_past_laplace_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      Measurable[𝓕 (n : ℝ≥0)] (fun ω : Ω => Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))) := by sorry
