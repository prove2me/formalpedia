-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_terminalRay_admission_edge
-- name    : DeciSigma1.Holes.Tail.terminalRay_admission_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:30.742591+00:00
-- url     : https://prove2.me/theorems/33d103ed-2962-4c4d-8ee1-91c75beecd8c
-- title:
--   Tail: terminal Ray admission edge
-- statement:
--   A constraint of the ray system between two rays that contain their whole original words
--   holds at the lengths of the original words.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L222-L241
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L222-L241

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

theorem DeciSigma1.Holes.Tail.terminalRay_admission_edge {M : StructuralReader α S k} {W : Fin k → List α}
    (hW : M.IsHole W) {i j : Fin k}
    {Ωi Ωj : Ray α} (hi : RayAgrees Ωi (W i) (W i).length)
    (hj : RayAgrees Ωj (W j) (W j).length) {a b : ℕ} (hb : b ≤ M.firstRejection W j)
    (hadm : M.admitted (rayState M (M.start i) Ωi a) (rayState M (M.start j) Ωj b) = true)
    (heq : ∀ t, Ωi.stream (a + t) = Ωj.stream (b + t)) :
    ((W i).length : ℤ) + ((b : ℤ) - a + 1) ≤ (W j).length := by sorry
