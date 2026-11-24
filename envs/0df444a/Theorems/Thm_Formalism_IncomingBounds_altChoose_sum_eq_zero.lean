-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_altChoose_sum_eq_zero
-- name    : Formalism.IncomingBounds.altChoose_sum_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:24.756405+00:00
-- url     : https://prove2.me/theorems/ab043864-4cc8-4205-a30e-24ae64a3ac51
-- title:
--   Incoming Bounds: alt Choose sum eq zero
-- statement:
--   The Incoming Bounds construction uses the alt Choose sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/AltChooseSumEqZero.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/AltChooseSumEqZero.lean#L10-L24

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_AltChooseSumEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset fwdDiff
open Formalism Formalism.IncomingBounds

theorem Formalism.IncomingBounds.altChoose_sum_eq_zero (D s y : ℕ) (hs : s ≤ D) :
    ∑ k ∈ range (D + 1 + 1), ((-1 : ℤ) ^ (D + 1 - k) * ((D + 1).choose k : ℤ)) *
      (((y + k).choose s : ℕ) : ℤ) = 0 := by sorry
