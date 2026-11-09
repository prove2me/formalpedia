-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_compensated_square_mean
-- name    : AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_compensated_square_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:16:05.456794+00:00
-- url     : https://prove2.me/theorems/46667cb1-9870-40a1-a4da-20bf96f5bae8
-- title:
--   Original stopped compensated Gaussian square has equal expectation at two ordered bounded grid stops
-- statement:
--   For the genuine zero-jump Gaussian source on its original probability space and natural right-continuous filtration, the compensated-square process Q has the same expectation at any two bounded ordered sampled stopping times on one physical grid.
-- source:
--   Exact original quadratic-martingale bounded two-stop conditional sampling a331e012, integral_condExp on the stopped-time sigma algebra; upstream of finite-cap Gaussian L2 energy and expected reward 50e1cf4c.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_compensated_square_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (grid i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (hgrid hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (grid i) } : Filtration ℕ mΩ))
    (α β : Ω → WithTop ℕ)
    (hα : IsStoppingTime 𝓖 α) (hβ : IsStoppingTime 𝓖 β)
    (hαβ : α ≤ β)
    (N : ℕ) (hbounded : ∀ ω, β ω ≤ (N : WithTop ℕ)) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
    let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
      (M t ω)^2 - (t : ℝ) * X.σ^2
    (∫ ω, stoppedValue (fun i : ℕ => Q (grid i)) α ω ∂P) =
    (∫ ω, stoppedValue (fun i : ℕ => Q (grid i)) β ω ∂P) := by sorry
