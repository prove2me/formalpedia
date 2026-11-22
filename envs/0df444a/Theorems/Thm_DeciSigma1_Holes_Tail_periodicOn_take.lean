-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_periodicOn_take
-- name    : DeciSigma1.Holes.Tail.periodicOn_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:05.365109+00:00
-- url     : https://prove2.me/theorems/1103d743-279a-4abd-992d-3f4db7c544ee
-- title:
--   Tail: periodic On take
-- statement:
--   The Tail construction uses the periodic On take property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L560-L564
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L560-L564

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.periodicOn_take {w : List α} {p s e n : ℕ} (h : PeriodicOn w p s e) (hen : e ≤ n) :
    PeriodicOn (w.take n) p s e := by sorry
