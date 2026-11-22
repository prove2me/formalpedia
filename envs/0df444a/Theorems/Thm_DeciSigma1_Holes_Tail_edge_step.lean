-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_edge_step
-- name    : DeciSigma1.Holes.Tail.edge_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:38.108731+00:00
-- url     : https://prove2.me/theorems/1f31a2d2-9354-4eae-a56f-e416a3612bcc
-- title:
--   Tail: edge step
-- statement:
--   A constraint `h → x` of the ray system into a ray `x` with `J x` before its onset aligns the
--   onsets and makes the stretch of `x` a suffix of the text of `h` before its onset.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L187-L203
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L187-L203

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
variable [DecidableEq α]

theorem DeciSigma1.Holes.Tail.edge_step {Ωh Ωx : Ray α} {a b Jx : ℕ} (heq : ∀ t, Ωh.stream (a + t) = Ωx.stream (b + t))
    (hb : b ≤ Jx) (hx : Jx < Ωx.onset) :
    Ωx.suffixBeforeOnset Jx <:+ Ωh.prefixBeforeOnset ∧ ∀ t, Ωh.stream (Ωh.onset + t) =
        Ωx.stream (Ωx.onset + t) := by sorry
