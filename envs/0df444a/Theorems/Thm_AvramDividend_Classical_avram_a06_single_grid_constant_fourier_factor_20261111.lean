-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_single_grid_constant_fourier_factor_20261111
-- name    : AvramDividend.Classical.avram_a06_single_grid_constant_fourier_factor_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:44:32.384347+00:00
-- url     : https://prove2.me/theorems/ec7b50d5-b9eb-4141-bed5-20c4459353fb
-- title:
--   One-coordinate random-grid Fourier factorisation with a constant length kernel
-- statement:
--   A one-coordinate random-vector Fourier function is automatically its scalar characteristic function. Set its random-length factor to the constant scalar characteristic function, independently of the length. Finite-family independence on a subsingleton and the probability-integral-of-constant identity yield both required equations. This is the n=1 component of A06 conditional Fourier representation.

import Mathlib
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_single_grid_constant_fourier_factor_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (D : Ω → ℕ) (Z : Ω → ℝ) (hZ : Measurable Z)
    (t : WithLp 2 (Fin 1 → ℝ)) :
    ∃ φ : Fin 1 → ℕ → ℂ,
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun _ : Fin 1 => Z ω)) P) t =
          ∫ ω, ∏ i : Fin 1, φ i (D ω) ∂P
      ∧ ∀ i : Fin 1, MeasureTheory.charFun (Measure.map Z P) (t.ofLp i) =
          ∫ ω, φ i (D ω) ∂P := by sorry
