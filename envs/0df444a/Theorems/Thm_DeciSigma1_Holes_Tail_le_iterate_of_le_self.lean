-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_le_iterate_of_le_self
-- name    : DeciSigma1.Holes.Tail.le_iterate_of_le_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:19.475181+00:00
-- url     : https://prove2.me/theorems/f01b9905-758d-4389-b20c-de83536037f9
-- title:
--   Tail: le iterate of le self
-- statement:
--   The Tail construction uses the le iterate of le self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L90-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L90-L93

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.le_iterate_of_le_self {f : ℕ → ℕ} (hf : ∀ b, b ≤ f b) (n b : ℕ) : b ≤ f^[n] b := by sorry
