-- Prove2me | Theorems.Thm_ChromaticReconstruction_card_key_fiber
-- name    : ChromaticReconstruction.card_key_fiber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T14:35:35.849849+00:00
-- url     : https://prove2.me/theorems/b3a1fd01-f7a1-4a87-b119-b8e91397cd11
-- title:
--   Chromatic Reconstruction: card key fiber
-- statement:
--   The Chromatic Reconstruction construction uses the card key fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L248-L307
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L248-L307

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]
variable {S : SimpleGraph K} {w : K → ℕ}

theorem ChromaticReconstruction.card_key_fiber (hS : S.Connected) (hk : 3 ≤ Fintype.card K) (hMI : MIso S w)
    (a : ℕ) (M : Multiset ℕ) :
    #{x | keyOf S w x = (a, M)} = fiberInv (wts w) (edgeTypes S w) a M := by sorry
