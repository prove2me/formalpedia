-- Prove2me | solution 1 for mme_CW_2376_auxiliary_profile_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T15:56:53.180347+00:00
-- url     : https://prove2.me/submissions/7cfaea5a-f656-4262-aa53-26e75d2180d2

import Mathlib.Tactic
import Definitions.Def_mme_CW_2376_profile_data

open MME

theorem solution
    (tau Vc : ℝ) :
    auxiliaryRHSWithCoupled 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d Vc =
      cw2376ProfileCountBase *
        cw2376ProfileNumeratorBase tau Vc := by
  unfold auxiliaryRHSWithCoupled cw2376ProfileCountBase
    cw2376ProfileNumeratorBase
  norm_num
  ring
