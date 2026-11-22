-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_terminalRay_no_selfAdmission
-- name    : DeciSigma1.Holes.Tail.terminalRay_no_selfAdmission
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:18.498514+00:00
-- url     : https://prove2.me/theorems/f1db7873-a611-4104-9ed1-48951ba2f78a
-- title:
--   Tail: terminal Ray no self Admission
-- statement:
--   A comparison of a terminal ray with itself is a comparison of the original word: in a
--   comparison of a word with itself the host cut is at most the target cut, so restricting it to
--   the original target suffix gives a comparison of the original word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L202-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L202-L218

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
variable [DecidableEq α] [DecidableEq S]

theorem DeciSigma1.Holes.Tail.terminalRay_no_selfAdmission {M : StructuralReader α S k} {W : Fin k → List α}
    (hW : M.IsHole W) {i : Fin k}
    {Ω : Ray α} (hΩ : RayAgrees Ω (W i) (W i).length) :
    ∀ a b, b ≤ M.firstRejection W i → a ≤ b →
      M.admitted (rayState M (M.start i) Ω a) (rayState M (M.start i) Ω b) = true →
      ¬ ∀ t, Ω.stream (a + t) = Ω.stream (b + t) := by sorry
