-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_iterate_add_const
-- name    : DeciSigma1.Holes.Tail.iterate_add_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:09.65708+00:00
-- url     : https://prove2.me/theorems/08786eff-d531-4d95-a3cb-a5e010f03f7b
-- title:
--   Tail: iterate add const
-- statement:
--   The Tail construction uses the iterate add const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L119-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L119-L121

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.iterate_add_const (h b0 : ℕ) : ∀ n, (fun b => b + h)^[n] b0 = b0 + n * h
  := by sorry
