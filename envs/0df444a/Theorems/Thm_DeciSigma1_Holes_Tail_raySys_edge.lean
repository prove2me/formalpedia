-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_raySys_edge
-- name    : DeciSigma1.Holes.Tail.raySys_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:40.255919+00:00
-- url     : https://prove2.me/theorems/a8a7c753-352c-46ff-8369-4605e555d219
-- title:
--   Tail: ray Sys edge
-- statement:
--   An edge of the ray system joins distinct rays with equal infinite suffixes at a target cut
--   `b ≤ J`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L209-L226
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L209-L226

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

theorem DeciSigma1.Holes.Tail.raySys_edge [Fintype ι] [DecidableEq ι] {M : StructuralReader α S k} {st : ι → S}
    {Ω : ι → Ray α} {J : ι → ℕ} {i j : ι} (h : ((raySystem M st Ω J).edgeWeight i j).isSome) :
    i ≠ j ∧ ∃ a b, b ≤ J j ∧ ∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t) := by sorry
