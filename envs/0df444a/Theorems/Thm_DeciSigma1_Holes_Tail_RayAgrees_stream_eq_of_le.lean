-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_RayAgrees_stream_eq_of_le
-- name    : DeciSigma1.Holes.Tail.RayAgrees.stream_eq_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:58.66612+00:00
-- url     : https://prove2.me/theorems/b2b29b48-2401-4807-b2ef-21a87eaa6412
-- title:
--   Ray Agrees: stream eq of le
-- statement:
--   Two rays that agree with the same word are equal if both ends lie at least the sum of the two
--   periods beyond both onsets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L69-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L69-L74

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

theorem DeciSigma1.Holes.Tail.RayAgrees.stream_eq_of_le [DecidableEq α] {Ω Ω' : Ray α} {x : List α} {E E' : ℕ}
    (h : RayAgrees Ω x E) (h' : RayAgrees Ω' x E')
    (hE : max Ω.onset Ω'.onset + Ω.period + Ω'.period ≤ min E E')
    (t : ℕ) : Ω.stream t = Ω'.stream t := by sorry
