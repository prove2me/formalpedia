-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_source_finitecap_Hessian_cross_expected_abs_L1
-- name    : AvramDividend.Classical.avram_ga_original_source_finitecap_Hessian_cross_expected_abs_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:10:16.136385+00:00
-- url     : https://prove2.me/theorems/2689fb0e-1d26-4ec4-bf3b-f0ec056f420d
-- title:
--   Original source finitecap Gaussian Hessian raw-centred cross tends to zero in expected absolute L1
-- statement:
--   Under the exact original finitecap positive-clock assumptions q≥0, w C2 on (0,C), strict pre-ruin floor delta>0, and Brownian/no-jump process, the source physical-grid active full-cell Hessian-weighted raw-minus-centred square term has vanishing expected absolute L1, assuming the explicit weighted term integrability. The deterministic coefficient-bound hypothesis needed by 7e470c61 is discharged by the newly Proved source-exact C2 clipping and postpayment floor theorem 1e33e963.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology

theorem AvramDividend.Classical.avram_ga_original_source_finitecap_Hessian_cross_expected_abs_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (j : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (Finset.range m).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω then
          Real.exp (-(q * (s : ℝ))) *
            (if x + X.X s ω - rightLimit D s ω ≤ b
             then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
             else 0) / 2 * (R ^ 2 - Z ^ 2)
        else 0)
    (∀ m, Integrable (fun ω => |B m ω|) P) →
    Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
