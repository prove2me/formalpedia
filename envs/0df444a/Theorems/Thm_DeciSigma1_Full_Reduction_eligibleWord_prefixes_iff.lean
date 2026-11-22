-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_eligibleWord_prefixes_iff
-- name    : DeciSigma1.Full.Reduction.eligibleWord_prefixes_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:16:37.215634+00:00
-- url     : https://prove2.me/theorems/bfee58b0-7173-4eaa-a154-3acffe9b3298
-- title:
--   Reduction: eligible Word prefixes iff
-- statement:
--   The Reduction construction uses the eligible Word prefixes iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L156-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L156-L163

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Readers
open DeciSigma1.Constraints DeciSigma1.Full.Closure
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
  {q : Fin k → V × V} {m : Fin k → Bool}

theorem DeciSigma1.Full.Reduction.eligibleWord_prefixes_iff (p r : V × Bool) (w : List (Fin n)) :
    (∀ a ≤ w.length, EligibleWord c Γ p r (w.take a)) ↔
      (r.1, r.2, w) ∉ leastClosure c Γ ∧ (p.1, !p.2, w) ∉ leastClosure c Γ := by sorry
