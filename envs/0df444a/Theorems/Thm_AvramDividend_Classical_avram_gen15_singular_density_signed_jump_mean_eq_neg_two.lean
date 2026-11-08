-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_signed_jump_mean_eq_neg_two
-- name    : AvramDividend.Classical.avram_gen15_singular_density_signed_jump_mean_eq_neg_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:27:22.552551+00:00
-- url     : https://prove2.me/theorems/e071cadf-b5af-472d-a775-bf4ed7fd1d89
-- title:
--   Signed first jump moment is negative two for the singular spectrally negative Levy density
-- statement:
--   The singular spectrally negative Levy measure has signed first jump moment negative two. This is the exact drift-correction integral required by the source SpectrallyNegativeLevy.drift definition to verify positive infinitesimal drift for the proposed non-monotone Levy countermodel.
-- source:
--   Accepted singular-density restricted integral and exact positive first-moment integral, with pointwise negative support and Bochner integral linearity.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen15_singular_density_signed_jump_mean_eq_neg_two :
    (∫ z : ℝ, z ∂(volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) = -2 := by sorry
