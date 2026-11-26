-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ofFn_rev
-- name    : FirstPassageLinearTransport.ofFn_rev
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:29:29.577806+00:00
-- url     : https://prove2.me/theorems/af0b49c9-f372-4526-86af-b51d46153757
-- title:
--   First Passage Linear Transport: of Fn rev
-- statement:
--   The First Passage Linear Transport construction uses the of Fn rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1306-L1319
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1306-L1319

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.ofFn_rev {r : ℕ} (v : Fin r → Bool) :
    List.ofFn (fun i => v (Fin.rev i)) = (List.ofFn v).reverse := by sorry
