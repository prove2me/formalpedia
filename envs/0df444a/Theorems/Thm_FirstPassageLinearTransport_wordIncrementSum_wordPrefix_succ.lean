-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_wordPrefix_succ
-- name    : FirstPassageLinearTransport.wordIncrementSum_wordPrefix_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:34:07.271097+00:00
-- url     : https://prove2.me/theorems/dc86041e-4b71-46e2-9066-b32cd1327e7c
-- title:
--   First Passage Linear Transport: word Increment Sum word Prefix succ
-- statement:
--   The First Passage Linear Transport construction uses the word Increment Sum word Prefix succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1355-L1368
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1355-L1368

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.wordIncrementSum_wordPrefix_succ
    {r : ℕ} (x : Bool → ℝ) (v : Fin (r + 1) → Bool)
    (j : Fin (r + 1)) :
    wordIncrementSum x (wordPrefix v j.succ) =
      x (v 0) + wordIncrementSum x
        (wordPrefix (fun i => v i.succ) j) := by sorry
