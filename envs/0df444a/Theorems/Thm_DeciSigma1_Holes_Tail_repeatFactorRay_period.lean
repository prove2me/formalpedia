-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_repeatFactorRay_period
-- name    : DeciSigma1.Holes.Tail.repeatFactorRay_period
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:29.376042+00:00
-- url     : https://prove2.me/theorems/5e4a12e3-f8d6-4730-af77-618d2ae84f4e
-- title:
--   Tail: repeat Factor Ray period
-- statement:
--   The ray of a factor closed at window `B` is periodic with the factor length from `c - B`
--   on.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L82-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L82-L92

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
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}

theorem DeciSigma1.Holes.Tail.repeatFactorRay_period (hcl : ClosedAt T q0 x B c c') :
    ∀ p, c - B ≤ p → (repeatFactorRay x c c' hcl.2.1 hcl.2.2.1).stream (p + (c' - c)) =
      (repeatFactorRay x c c' hcl.2.1 hcl.2.2.1).stream p := by sorry
