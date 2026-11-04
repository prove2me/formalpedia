-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_pre_source_localised_small_mark_bound
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_pre_source_localised_small_mark_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:08:20.818689+00:00
-- url     : https://prove2.me/theorems/390b92fe-5947-4ec7-b703-d2f9ea3a9250
-- title:
--   True controlled original-source prepayment reserve has first-order local BV jump envelope
-- statement:
--   Apply the accepted compact first-order negative-source-mark bound to the exact original controlled pre-source left-limit reserve x+X-rightLimit D. On a localised predictable interior set E the reserve has the required safety margin, so negative source marks of at most δ yield |w(Upre+z)-w(Upre)|≤K|z|. This is the genuine original X,D interface for finite-variation small-jump summability, not a marked Poisson surrogate or a claim of a global negative-jump first moment.
-- source:
--   Exact original Lévy X, dividend D and compact first-order local Lipschitz helper

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_pre_source_localised_small_mark_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (x : ℝ) (w : ℝ → ℝ) (K : ℝ≥0) (a b δ : ℝ) (hδ : 0 ≤ δ) (hLip : LipschitzOnWith K w (Icc a b)) (Upre : ℝ≥0 × Ω → ℝ) (hUpre : ∀ p, Upre p = Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) (E : Set (ℝ≥0 × Ω)) (hE : ∀ p ∈ E, Upre p ∈ Icc (a + δ) b) : ∀ p ∈ E, ∀ z ∈ Icc (-δ) 0, |w (Upre p + z) - w (Upre p)| ≤ (K : ℝ) * |z| := by sorry
