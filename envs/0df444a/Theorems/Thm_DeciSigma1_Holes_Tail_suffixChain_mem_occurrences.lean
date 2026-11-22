-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixChain_mem_occurrences
-- name    : DeciSigma1.Holes.Tail.suffixChain_mem_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:50.348868+00:00
-- url     : https://prove2.me/theorems/c70f8b01-7deb-49e4-b4a9-3b86c67f140e
-- title:
--   Tail: suffix Chain mem occurrences
-- statement:
--   Along a suffix chain of `t` with first member `b₀ ≥ b`, the member `b' ≤ |t|` gives an
--   occurrence of the suffix of length `b` ending at `|t| - b' + b₀`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/WindowChains.lean#L249-L260
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/WindowChains.lean#L249-L260

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
variable [DecidableEq α]

theorem DeciSigma1.Holes.Tail.suffixChain_mem_occurrences {t : List α} {b b₀ b' : ℕ} {bs : List ℕ}
    (h : SuffixChain t (b₀ :: bs)) (hb : b ≤ b₀) (hb' : b' ∈ b₀ :: bs) (hle : b' ≤ t.length) :
    t.length - b' + b₀ ∈ occurrences t t b := by sorry
