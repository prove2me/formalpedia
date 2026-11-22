-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_compatible_symm
-- name    : DeciSigma1.Holes.Tail.compatible_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:34.771804+00:00
-- url     : https://prove2.me/theorems/f4f7d6fd-0995-4abc-8b0d-d1f9f84c3d72
-- title:
--   Tail: compatible symm
-- statement:
--   For two rays that are not periodic at their first rejected cuts, the absence of forbidden
--   overlaps is symmetric.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L175-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L175-L183

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

theorem DeciSigma1.Holes.Tail.compatible_symm {Ωv Ωu : Ray α} {Jv Ju : ℕ} (hv : Jv < Ωv.onset) (hu : Ju < Ωu.onset)
    (h : NoForbiddenRayOverlap Ωv Ωu Jv Ju) : NoForbiddenRayOverlap Ωu Ωv Ju Jv := by sorry
