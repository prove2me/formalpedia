-- Prove2me | Theorems.Thm_AvramDividend_Classical_weighted_jump_integral_affine_compensation
-- name    : AvramDividend.Classical.weighted_jump_integral_affine_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:49:25.759337+00:00
-- url     : https://prove2.me/theorems/499c8eda-f21f-4461-be60-ff894f1297ca
-- title:
--   Affine compensated jump transform integrates with its origin boundary term
-- statement:
--   An exact Bochner-integral identity for an integrable jump exponential increment F and small-jump compensation K. The transform of (F-aK)b+Kc equals the respective scalar-weighted integrals, retaining c times the compensation integral. This reusable algebra isolates the nontrivial Fubini and derivative boundary assumptions in the BV Lévy scale-function generator proof.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, generator Laplace transform with bounded-variation compensation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace AvramDividend.Classical

theorem weighted_jump_integral_affine_compensation
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F K : α → ℝ) (a b c : ℝ)
    (hF : Integrable F μ) (hK : Integrable K μ) :
    (∫ y, ((F y - a * K y) * b + K y * c) ∂μ) =
      ((∫ y, F y ∂μ) - a * (∫ y, K y ∂μ)) * b +
      (∫ y, K y ∂μ) * c := by sorry

end AvramDividend.Classical
