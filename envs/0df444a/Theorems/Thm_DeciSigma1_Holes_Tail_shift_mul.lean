-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_shift_mul
-- name    : DeciSigma1.Holes.Tail.shift_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:38.099535+00:00
-- url     : https://prove2.me/theorems/c605685b-3459-44a7-b2ef-d7dbc4606d83
-- title:
--   Tail: shift mul
-- statement:
--   If `h` is a period of `f` from position `A` on, so is every multiple of `h`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L65-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L65-L72

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

theorem DeciSigma1.Holes.Tail.shift_mul {f : ℕ → α} {A h : ℕ} (hper : ∀ p, A ≤ p → f (p + h) = f p) :
    ∀ j p, A ≤ p → f (p + j * h) = f p := by sorry
