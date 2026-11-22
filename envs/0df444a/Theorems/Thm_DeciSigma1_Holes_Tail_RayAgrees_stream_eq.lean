-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_RayAgrees_stream_eq
-- name    : DeciSigma1.Holes.Tail.RayAgrees.stream_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:34.197071+00:00
-- url     : https://prove2.me/theorems/8053ec14-b091-4a7c-a059-b1404dfbdc03
-- title:
--   Ray Agrees: stream eq
-- statement:
--   Two rays that agree with the same word agree with each other below both ends.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L63-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L63-L65

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

theorem DeciSigma1.Holes.Tail.RayAgrees.stream_eq {Ω Ω' : Ray α} {x : List α} {E E' t : ℕ} (h : RayAgrees Ω x E)
    (h' : RayAgrees Ω' x E') (ht : t < E) (ht' : t < E') : Ω.stream t = Ω'.stream t := by sorry
