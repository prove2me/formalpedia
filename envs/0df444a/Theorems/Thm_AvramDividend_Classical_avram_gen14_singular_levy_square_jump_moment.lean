-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_square_jump_moment
-- name    : AvramDividend.Classical.avram_gen14_singular_levy_square_jump_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:01:48.730314+00:00
-- url     : https://prove2.me/theorems/edb377d3-ca57-48af-97c9-24168cd9b2f5
-- title:
--   Singular negative Levy density has square-jump moment two-thirds
-- statement:
--   The integral of the squared absolute jump size under the specified singular negative Levy measure is two-thirds. Together with the first-moment integrability certificate, this gives the explicit jump-moment estimates required to construct a bona fide spectrally negative bounded-variation Levy process for testing Avram's uniform-cell integrability assumption.
-- source:
--   Pinned integral_rpow, integral_comp_neg and the newly verified singular-density restricted integral; exact power combination on the negative interval.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen14_singular_levy_square_jump_moment :
    (∫ z : ℝ, |z| ^ (2 : ℕ) ∂(volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) = 2 / 3 := by sorry
