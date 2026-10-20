-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_infinite_small_jumps
-- name    : AvramDividend.Classical.scaleFunction_zero_origin_infinite_small_jumps
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T22:55:46.207171+00:00
-- url     : https://prove2.me/theorems/1f6cbd4d-f910-47bb-ab44-c654d32fe769
-- title:
--   Infinite small-negative-jump first moment forces zero canonical scale function at the origin
-- statement:
--   Under zero Gaussian coefficient and infinite small-negative-jump absolute first moment, the normalised Lévy exponent eventually exceeds any real threshold. The resulting superlinear growth forces the canonical q-scale function to vanish at zero for q>0. Neither Standing nor integrability of the full process increment is required.
-- source:
--   Composition of psi_normalised_unbounded_small_jumps and scaleFunction_origin_zero_of_superlinear_psi, developed in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_zero_origin_infinite_small_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    W 0 = 0 := by sorry
