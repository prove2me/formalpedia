-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_increment_orthogonal
-- name    : AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_increment_orthogonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:42:12.290889+00:00
-- url     : https://prove2.me/theorems/ccc2e577-ea30-4549-8348-4f6543605f65
-- title:
--   Original stopped Gaussian increment has zero cross moment with earlier stopped value
-- statement:
--   For two ordered bounded physical-grid stopping indices on the original zero-jump Gaussian source and its right-continuous filtration, the expectation of the earlier centred source times the later-minus-earlier centred increment vanishes; square integrability, adaptiveness and product integrability are derived rather than assumed.
-- source:
--   Combine public Proved original cross-moment c3087a6e and the bounded-stopping L2 premise package avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability. Integrability legitimises linearity of the integral. Upstream of actual Gaussian Ito energy for 50e1cf4c.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_cross_moment
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_increment_orthogonal
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
    let A := stoppedValue (fun i : ℕ => M (grid i)) α
    let B := stoppedValue (fun i : ℕ => M (grid i)) β
    (∫ ω, A ω * (B ω - A ω) ∂P) = 0 := by sorry
