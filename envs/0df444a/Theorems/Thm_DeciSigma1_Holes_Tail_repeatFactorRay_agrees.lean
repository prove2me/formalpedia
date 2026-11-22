-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_repeatFactorRay_agrees
-- name    : DeciSigma1.Holes.Tail.repeatFactorRay_agrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:51.268835+00:00
-- url     : https://prove2.me/theorems/2122d81c-29ed-4dd9-9382-6a077420c9ac
-- title:
--   Tail: repeat Factor Ray agrees
-- statement:
--   The ray of a factor agrees with the original word up to the end of the factor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L84-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L84-L91

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

theorem DeciSigma1.Holes.Tail.repeatFactorRay_agrees {x : List α} {c c' : ℕ} (hcc : c < c') (hc' : c' ≤ x.length) :
    RayAgrees (repeatFactorRay x c c' hcc hc') x c' := by sorry
