-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_periodicOn_of_rayAgrees
-- name    : DeciSigma1.Holes.Tail.periodicOn_of_rayAgrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:53.539894+00:00
-- url     : https://prove2.me/theorems/0f2ec26a-1520-4332-aca9-748c79267ba7
-- title:
--   Tail: periodic On of ray Agrees
-- statement:
--   A ray agreeing with a word is periodic there from its onset.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L56-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L56-L62

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

theorem DeciSigma1.Holes.Tail.periodicOn_of_rayAgrees [DecidableEq α] {Ω : Ray α} {x : List α} {E : ℕ}
    (h : RayAgrees Ω x E) : PeriodicOn x Ω.period Ω.onset E := by sorry
