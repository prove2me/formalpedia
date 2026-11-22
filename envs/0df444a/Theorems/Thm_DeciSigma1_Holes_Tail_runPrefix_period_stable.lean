-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_runPrefix_period_stable
-- name    : DeciSigma1.Holes.Tail.runPrefix_period_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:09.029881+00:00
-- url     : https://prove2.me/theorems/e9043750-7f74-4393-b65d-6c75e3b80839
-- title:
--   Tail: run Prefix period stable
-- statement:
--   On an interval `[s, e)` of period `p`, the states at cuts `x ≥ s + N · p` repeat after
--   `p · N!` letters.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L97-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L97-L117

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

theorem DeciSigma1.Holes.Tail.runPrefix_period_stable [Fintype S] (T : Table α S k) (W : Fin k → List α) (i : Fin k)
    {p s e x : ℕ} (hp : 0 < p) (hper : PeriodicOn (W i) p s e) (he : e ≤ (W i).length)
    (hx : s + Fintype.card S * p ≤ x) (hxe : x + p * (Fintype.card S).factorial ≤ e) :
    T.runPrefix W i (x + p * (Fintype.card S).factorial) = T.runPrefix W i x := by sorry
