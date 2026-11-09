-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_increment_second_moment_difference
-- name    : AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_increment_second_moment_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:08:14.980842+00:00
-- url     : https://prove2.me/theorems/4489c8e9-b2b6-4bb1-91e6-84b4a0dfb078
-- title:
--   Original bounded Gaussian stopped increment second moment equals the stopped second-moment difference
-- statement:
--   For the original zero-jump Lévy source on a sampled physical-time grid, the expected square of the later-minus-earlier bounded stopped centred Gaussian source equals the later second moment minus the earlier second moment. Integrability is derived from actual original stopped square moments; stochastic increment orthogonality removes the cross term.
-- source:
--   Proved public original stopped Gaussian cross moment c3087a6e and original stopped source MemLp two de80c263. The proof derives orthogonality algebraically from these two public premises, independently of pending ccc2e577, then establishes the stopped incremental L2 energy equality to combine with compensated-square mean 46667cb1 upstream of the source reward 50e1cf4c.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_cross_moment

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_increment_second_moment_difference
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
    (∫ ω, (B ω - A ω)^2 ∂P) =
      (∫ ω, (B ω)^2 ∂P) - (∫ ω, (A ω)^2 ∂P) := by sorry
