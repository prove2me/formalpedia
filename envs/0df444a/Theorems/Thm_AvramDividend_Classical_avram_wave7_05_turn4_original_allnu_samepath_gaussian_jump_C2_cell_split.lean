-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_cell_split
-- name    : AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_cell_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:44:14.624939+00:00
-- url     : https://prove2.me/theorems/62a48d60-127c-4fff-af13-dcd1049607c8
-- title:
--   Exact original-source arbitrary-jump C2 Gaussian residual and jump cell algebraic split
-- statement:
--   With the canonical Lévy X, dividend control D, its true ruin mask, real predividend reserve and arbitrary ν, assume explicitly a same-path decomposition X_t=t*c+M_t+Jsmall_t+Jlarge_t. Then every source stopped C² Gaussian Taylor cell exactly splits into the centred continuous residual C² cell with σ²/2 and the jump derivative, mixed Hessian and square jump remainder. This is a genuine pathwise identity conditional on the unproved source Lévy–Itô decomposition, with no assertion that M is yet a local martingale.
-- source:
--   Canonical exact original X.X, ruinTime, rightLimit D and one-sided positive-interior capped Hessian; conditional source bridge hypothesis to be discharged from original intrinsic marked jump measure UUID 409ca60f-48af-4148-a44b-dd3d91c39af7 and W7-01 rate UUID 859bf7be-1e5d-40c6-98fa-b438f19735af.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_cell_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (M Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c + M t ω + Jsmall t ω + Jlarge t ω)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (h : ℝ≥0) :
    let G : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let H : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let A : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let B : Ω → ℝ := fun ω =>
      M (τ ω + h) ω - M (τ ω) ω
    let J : Ω → ℝ := fun ω =>
      (Jsmall (τ ω + h) ω - Jsmall (τ ω) ω) +
      (Jlarge (τ ω + h) ω - Jlarge (τ ω) ω)
    ∀ ω,
      G ω * A ω + (1 / 2 : ℝ) * H ω * (A ω ^ 2 - (h : ℝ) * X.σ ^ 2) =
      (G ω * B ω + (1 / 2 : ℝ) * H ω *
        (B ω ^ 2 - (h : ℝ) * X.σ ^ 2)) +
      (G ω * J ω + H ω * B ω * J ω + (1 / 2 : ℝ) * H ω * J ω ^ 2) := by sorry
