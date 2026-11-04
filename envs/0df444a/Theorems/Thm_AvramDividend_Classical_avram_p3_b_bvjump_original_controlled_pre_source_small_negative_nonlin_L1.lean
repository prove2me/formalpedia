-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_pre_source_small_negative_nonlin_L1
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_pre_source_small_negative_nonlin_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:16:19.632023+00:00
-- url     : https://prove2.me/theorems/18ea6669-24b3-40a0-987f-2595616fbb9f
-- title:
--   Original controlled BV prepayment reserve has ν-integrable small nonlinear source jumps
-- statement:
--   At every time/path point of a genuine original-process interior localisation E, the controlled source pre-payment reserve Upre = leftLim(x + X - rightLimit D) lies a full unit inside the compact interval [a,b]. The accepted original source BV first-moment and automatic measurability lemma applied at Upre proves ν-integrability of z↦w(Upre+z)-w(Upre) on (-1,0), with no independent marked Poisson model and no untruncated large negative first moment.
-- source:
--   Accepted original BV small nonlinear L1 automatic measurability and exact controlled pre-source reserve

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_nonlin_L1_of_local_Lipschitz
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_pre_source_small_negative_nonlin_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (x : ℝ) (w : ℝ → ℝ) (K : ℝ≥0) (a b : ℝ) (hLip : LipschitzOnWith K w (Icc a b)) (Upre : ℝ≥0 × Ω → ℝ) (hUpre : ∀ p, Upre p = Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) (E : Set (ℝ≥0 × Ω)) (hE : ∀ p ∈ E, Upre p ∈ Icc (a + 1) b) : ∀ p ∈ E, IntegrableOn (fun z : ℝ => w (Upre p + z) - w (Upre p)) (Ioo (-1 : ℝ) 0) X.ν := by sorry
