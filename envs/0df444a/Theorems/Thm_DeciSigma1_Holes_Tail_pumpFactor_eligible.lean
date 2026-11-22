-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_eligible
-- name    : DeciSigma1.Holes.Tail.pumpFactor_eligible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:46.323888+00:00
-- url     : https://prove2.me/theorems/8bb0e18c-fde7-4d27-8034-e021755ca0b1
-- title:
--   Tail: pump Factor eligible
-- statement:
--   Replacing an eligible word by a pumped closed factor after its first rejected cut gives an
--   eligible word with an immortal endpoint and the same first rejected cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L757-L807
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L757-L807

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.pumpFactor_eligible [DecidableEq α] (M : StructuralReader α S k)
    {W W' : Fin k → List α} {i : Fin k} {D : Finset (List α)} {c c' L : ℕ} (hW : M.Eligible W i)
    (hcl : NodeClosedAt M.toTable (M.start i) D (W i) c c') (hJ : M.firstRejection W i ≤ c)
    (hL : c' - c ≤ L) (hW' : W' i = pumpFactor (W i) c c' L) :
    M.Eligible W' i ∧ M.Immortal (M.endState W' i) ∧ M.firstRejection W' i =
        M.firstRejection W i := by sorry
