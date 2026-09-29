-- Prove2me | solution 1 for mme_CW_endpoint_of_numeric_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T07:59:35.786709+00:00
-- url     : https://prove2.me/submissions/13019bf6-7ac6-4afb-a5d8-f9ff9201d7c2

import Definitions.Def_mme_CW_auxiliary_RHS
import Theorems.Thm_mme_CW_auxiliary_mono

open MME

/-!
# Reusable endpoint comparison for the exact CW profile

Any strict numerical certificate at a candidate exponent `c` can be combined
with the already-proved monotonicity of the exact `q = 6` auxiliary expression
to rule out every exponent `w >= c` satisfying the CW auxiliary upper bound.
-/

theorem solution
    (c w : ℝ)
    (hnumeric :
      (64 : ℝ) <
        auxiliaryRHS 6 (c / 3) cw2376_a cw2376_b cw2376_c cw2376_d)
    (haux :
      auxiliaryRHS 6 (w / 3) cw2376_a cw2376_b cw2376_c cw2376_d ≤ 64) :
    w < c := by
  by_contra hw
  rw [not_lt] at hw
  have htau : c / 3 ≤ w / 3 := by linarith
  have hmono := mme_CW_auxiliary_mono (c / 3) (w / 3) htau
  linarith
