-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_translate
-- name    : DeciSigma1.Holes.Fresh.previousAnchor_translate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:00.54598+00:00
-- url     : https://prove2.me/theorems/0b343e75-889f-4ca5-b338-a078865c9df1
-- title:
--   Fresh: previous Anchor translate
-- statement:
--   The Fresh construction uses the previous Anchor translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L443-L468
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L443-L468

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}

theorem DeciSigma1.Holes.Fresh.previousAnchor_translate {A : Finset ℕ} {s e q : ℕ}
    (hs : s = 0 ∨ s ∈ A) (hsq : s < q) (hqe : q ≤ e) :
    previousAnchor A q = s + previousAnchor (relativeCuts A s e) (q - s) := by sorry
