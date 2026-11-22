-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_rayState_eq_runPrefix
-- name    : DeciSigma1.Holes.Tail.rayState_eq_runPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:43.844962+00:00
-- url     : https://prove2.me/theorems/8676ea8e-6d78-46bc-85ba-8436f1d1d178
-- title:
--   Tail: ray State eq run Prefix
-- statement:
--   States along a ray that agrees with the word of coordinate `i` are the original states.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L77-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L77-L81

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

theorem DeciSigma1.Holes.Tail.rayState_eq_runPrefix (M : StructuralReader α S k) {W : Fin k → List α} {i : Fin k}
    {Ω : Ray α}
    {E a : ℕ} (h : RayAgrees Ω (W i) E) (ha : a ≤ E) :
    rayState M (M.start i) Ω a = M.runPrefix W i a := by sorry
