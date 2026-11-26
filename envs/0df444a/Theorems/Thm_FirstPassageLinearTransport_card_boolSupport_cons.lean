-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
-- name    : FirstPassageLinearTransport.card_boolSupport_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:27:19.479714+00:00
-- url     : https://prove2.me/theorems/9794997e-b3f1-406a-a144-01a0693edaff
-- title:
--   First Passage Linear Transport: card bool Support cons
-- statement:
--   The First Passage Linear Transport construction uses the card bool Support cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2720-L2729
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2720-L2729

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.card_boolSupport_cons
    {r : ℕ} (b : Bool) (w : Fin r → Bool) :
    (boolSupport (Fin.cons b w)).card =
      (if b then 1 else 0) + (boolSupport w).card := by sorry
