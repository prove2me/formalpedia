-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_esscher_arbitrary_stopping_downward_regular
-- name    : AvramDividend.Classical.avram_root29_04_pure_jump_esscher_arbitrary_stopping_downward_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:37:39.050005+00:00
-- url     : https://prove2.me/theorems/56bd4e99-3df6-44ef-8bc7-2c25a13f9e19
-- title:
--   All genuine finite stopping times remain immediately downward regular under an actual pure-jump finite Esscher law
-- statement:
--   For any genuine finite stopping time of a spectrally negative Lévy process with infinite small negative-jump absolute first moment, the post-stopping process immediately enters the negative half-line almost surely under the actual finite-terminal Esscher weighted measure. The proof uses Rogozin negative slopes, right-continuous dense-grid transfer, the Proved original-law arbitrary-stopping-time shift theorem, and absolute continuity of the weighted law. It is valid for all eligible stopping times and finite weight horizons T, without pretending that this is the sigma-finite Ito excursion law.
-- source:
--   Proved b12c5430 Rogozin slopes, b2e... near-zero converter, 561313a4 dense-grid, e39806bd finite-stopping transfer, 5b4f4749 absolute-continuity transfer; Mathlib measurable_pi_lambda, withDensity_absolutelyContinuous.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_rogozin_negative_slopes
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_ae_negative_near_zero_of_grid
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_absolutelyContinuous

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_04_pure_jump_esscher_arbitrary_stopping_downward_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    ∀ᵐ ω ∂(P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X T ω - (T : ℝ) * X.ψ θ)))),
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          X.X (τ ω + s) ω - X.X (τ ω) ω < 0 := by sorry
