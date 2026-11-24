-- Prove2me | Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_cplx_bound
-- name    : Formalism.MainNotions.WeightedLatticeSum.cplx_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:06.347103+00:00
-- url     : https://prove2.me/theorems/78b3a3d5-aeb0-4588-acca-84be6283f05f
-- title:
--   Weighted Lattice Sum: cplx bound
-- statement:
--   The Weighted Lattice Sum construction uses the cplx bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L189-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L189-L199

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.WeightedLatticeSum
open Finset

theorem Formalism.MainNotions.WeightedLatticeSum.cplx_bound (R : ℝ) (hR : 0 < R) (z : ℂ) :
    (max 1 (‖z‖ / R)) ^ (-(3 : ℝ)) ≤
      (max 1 (|z.re| / R)) ^ (-(3 / 2 : ℝ)) * (max 1 (|z.im| / R)) ^ (-(3 / 2 : ℝ)) := by sorry
