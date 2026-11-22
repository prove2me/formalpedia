-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_not_mem_closed_walk_of_noForbiddenRayOverlap
-- name    : DeciSigma1.Holes.Tail.not_mem_closed_walk_of_noForbiddenRayOverlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:54.015602+00:00
-- url     : https://prove2.me/theorems/7e0b715e-fba4-4fae-a208-912e0cf1752c
-- title:
--   Tail: not mem closed walk of no Forbidden Ray Overlap
-- statement:
--   A ray `v` that is not periodic at its first rejected cut and has no forbidden overlap with
--   any other ray lies on no closed walk of the ray system.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L303-L320
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L303-L320

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
variable {ι : Type} [Fintype S]
variable [Fintype ι] [DecidableEq ι] (M : StructuralReader α S k) (st : ι → S) (Ω : ι → Ray α)
  (J : ι → ℕ) (v : ι)
variable {M st Ω J v}

theorem DeciSigma1.Holes.Tail.not_mem_closed_walk_of_noForbiddenRayOverlap (hv : J v < (Ω v).onset)
    (hclean : ∀ u, u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u))
    {i : ι} {p : List ι} (hw : (raySystem M st Ω J).IsWalk (i :: p ++ [i])) : v ∉ i :: p := by sorry
