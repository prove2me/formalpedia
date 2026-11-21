-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_UBV_zero_discount_scale_exists
-- name    : AvramDividend.Classical.avram_f6_purejump_UBV_zero_discount_scale_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:40:59.964669+00:00
-- url     : https://prove2.me/theorems/d4f7a149-5d51-4d17-95b0-e568ea3b01b6
-- title:
--   Original pure-jump infinite-variation Lévy process admits its zero-discount scale function
-- statement:
--   For an original standing unbounded-variation spectrally negative Lévy process with vanishing Gaussian coefficient, construct the zero-discount q-scale function W^(0), zero on negative arguments, nonnegative continuous and monotone on nonnegative arguments, with Laplace transform 1/ψ(θ) at positive θ satisfying ψ(θ)>0. The construction requires the genuine pure-jump ascending ladder-height potential or a sound equivalent renewal representation; abstract existence alone is the mathematical obligation. This is the sigma-zero branch of the existing original UBV zero-discount scale-existence theorem 5b8fc9b8-6325-49fd-8e0c-77bd3bb315e7. Its sigma-positive branch is existing Open theorem 1cb0205e-841b-45cd-b26e-4276feaab780. The parent bridge is a case split using σ≥0, with no reverse imports.
-- source:
--   Avram–Palmowski–Pistorius (2007), spectrally negative Lévy q-scale foundation; Kyprianou fluctuation theory ladder-height renewal construction of W^(0). Root-connected source obligation for mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_purejump_UBV_zero_discount_scale_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    ∃ W₀ : ℝ → ℝ, IsScaleFunction X 0 W₀ := by sorry
