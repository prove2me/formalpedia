-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_compile_liveAlong_iff
-- name    : DeciSigma1.Full.Reduction.compile_liveAlong_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:17:04.441251+00:00
-- url     : https://prove2.me/theorems/cb6d340f-2fcf-4a34-8b00-374e8e6af637
-- title:
--   Reduction: compile live Along iff
-- statement:
--   The Reduction construction uses the compile live Along iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L165-L177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L165-L177

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

theorem DeciSigma1.Full.Reduction.compile_liveAlong_iff (W : Fin k → List (Fin n)) (i : Fin k) :
    (∀ a ≤ (W i).length, (compile c Γ q m).runPrefix W i a ≠ none) ↔
      exclusion (q i) (m i) (W i) ∉ leastClosure c Γ ∧
        flipC (seed (q i) (m i) (W i)) ∉ leastClosure c Γ := by sorry
