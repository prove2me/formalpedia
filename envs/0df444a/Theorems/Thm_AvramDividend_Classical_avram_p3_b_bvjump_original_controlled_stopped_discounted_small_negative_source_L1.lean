-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_stopped_discounted_small_negative_source_L1
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_stopped_discounted_small_negative_source_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:22:02.790711+00:00
-- url     : https://prove2.me/theorems/eba45787-b47e-41f7-be67-59e2245888c9
-- title:
--   Original bounded stopped controlled-reserve discounted nonlinear small marks are ν-integrable
-- statement:
--   On the same original Ω, P, filtration, source X, original dividend D and a genuinely bounded right-continuous-filtration stopping time τ, the stopped discounted original nonlinear source kernel is ν-integrable in each negative small mark z∈(-1,0), at every time-path point. It uses the actual pre-payment left-limit reserve and a compact one-unit interior localisation. It follows from the source-exact pre-state BV nonlinear L1 and preserves the clock/payment ordering, without independently proving a P2 compensated jump expectation.
-- source:
--   Accepted original controlled pre-source small nonlinear L1, bounded original stopped clock and exact rightLimit D convention

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_pre_source_small_negative_nonlin_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal Classical

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_stopped_discounted_small_negative_source_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (x : ℝ) (w : ℝ → ℝ) (K : ℝ≥0) (a b q : ℝ) (hLip : LipschitzOnWith K w (Icc a b)) (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T) (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (Upre : ℝ≥0 × Ω → ℝ) (hUpre : ∀ p, Upre p = Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) (E : Set (ℝ≥0 × Ω)) (hE : ∀ p ∈ E, Upre p ∈ Icc (a + 1) b) : ∀ p : ℝ≥0 × Ω, IntegrableOn (fun z : ℝ => if p ∈ E ∧ p.1 ≤ τ p.2 then Real.exp (-(q * (p.1 : ℝ))) * (w (Upre p + z) - w (Upre p)) else 0) (Ioo (-1 : ℝ) 0) X.ν := by sorry
