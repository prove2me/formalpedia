-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_levelCoverProperty_chainBoundFrom
-- name    : DeciSigma1.Holes.Tail.levelCoverProperty_chainBoundFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:49.089191+00:00
-- url     : https://prove2.me/theorems/d32b6a7a-512d-41b3-b9d9-c21abb27fb2b
-- title:
--   Tail: level Cover Property chain Bound From
-- statement:
--   A word with the level cover property at level `m` has suffix chains of at most
--   `pieceCountBase + N` steps from every window at least
--   `(pieceCountBase + 2) (chainLengthBound m + 1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/WindowChains.lean#L272-L330
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/WindowChains.lean#L272-L330

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable {σ : ℕ} [DecidableEq α] [Fintype S] [DecidableEq S]
omit [DecidableEq S]

theorem DeciSigma1.Holes.Tail.levelCoverProperty_chainBoundFrom (C : LevelBounds σ k (Fintype.card S))
    {M : StructuralReader α S k} {W : Fin k → List α} {i : Fin k} {m : ℕ} (h : M.Eligible W i)
    (hK : LevelCoverProperty C m M W i) {b₀ : ℕ}
    (hb : (C.pieceCountBase + 2) * (C.chainLengthBound m + 1) ≤ b₀) :
    ChainBoundFrom (W i) b₀ (C.pieceCountBase + Fintype.card S) := by sorry
