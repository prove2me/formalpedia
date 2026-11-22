-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_RunCovers_mono
-- name    : DeciSigma1.Holes.Tail.RunCovers.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:28.138599+00:00
-- url     : https://prove2.me/theorems/2c125c70-be17-490b-b334-d7f35d22a7e8
-- title:
--   Run Covers: mono
-- statement:
--   The Run Covers construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RunCovers.lean#L76-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RunCovers.lean#L76-L78

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.RunCovers.mono {rs runs : Finset (RunSpec k)} {i : Fin k} {p : ℕ} (h : RunCovers rs i p)
    (hsub : rs ⊆ runs) : RunCovers runs i p := by sorry
