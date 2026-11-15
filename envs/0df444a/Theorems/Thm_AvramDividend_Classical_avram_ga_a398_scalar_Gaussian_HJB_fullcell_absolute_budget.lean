-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a398_scalar_Gaussian_HJB_fullcell_absolute_budget
-- name    : AvramDividend.Classical.avram_ga_a398_scalar_Gaussian_HJB_fullcell_absolute_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:55:22.353933+00:00
-- url     : https://prove2.me/theorems/ff837f16-e6c9-4562-91f4-cd33aabbd5ca
-- title:
--   Scalar Gaussian HJB compensated second-order cell has an absolute quadratic envelope
-- statement:
--   A discounted compensated linear-quadratic expression with bounded derivative, Hessian and generator coefficients is controlled by a fixed multiple of the absolute centred increment, its square and the time increment.
-- source:
--   Gaussian A source a395 and a390, splitting scalar algebra from stochastic moment arguments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a398_scalar_Gaussian_HJB_fullcell_absolute_budget
    (M a E δ z u v g : ℝ) (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hδ : 0 ≤ δ)
    (hu : |u| ≤ M) (hv : |v| ≤ M) (hg : |g| ≤ M) :
    |E * (u * z + v / 2 * (z^2 - δ * a)) + δ * E * g| ≤
      M * (2 + a) * (|z| + z^2 + δ) := by sorry
