-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_compile_live_iff
-- name    : DeciSigma1.Full.Reduction.compile_live_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:16:25.919544+00:00
-- url     : https://prove2.me/theorems/6d78ffa2-10fc-40eb-8c1b-71cee977bae6
-- title:
--   Reduction: compile live iff
-- statement:
--   The Reduction construction uses the compile live iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L137-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L137-L143

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

theorem DeciSigma1.Full.Reduction.compile_live_iff (c : Fin n → Bool) (Γ : List (LitT n V)) (q : Fin k → V × V)
    (m : Fin k → Bool) (W : Fin k → List (Fin n)) (i : Fin k) {a : ℕ}
    (ha : a ≤ (W i).length) :
    (compile c Γ q m).runPrefix W i a ≠ none ↔
      ∀ a' ≤ a, EligibleWord c Γ (seedName (q i) (m i))
        (exclusionName (q i) (m i)) ((W i).take a') := by sorry
