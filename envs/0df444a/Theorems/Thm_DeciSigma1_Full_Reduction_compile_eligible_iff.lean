-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_compile_eligible_iff
-- name    : DeciSigma1.Full.Reduction.compile_eligible_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:17:03.775045+00:00
-- url     : https://prove2.me/theorems/fe133878-30c3-48f4-b366-c30946a2b6d3
-- title:
--   Reduction: compile eligible iff
-- statement:
--   The Reduction construction uses the compile eligible iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L186-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L186-L204

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

theorem DeciSigma1.Full.Reduction.compile_eligible_iff (W : Fin k → List (Fin n)) (i : Fin k) :
    (compile c Γ q m).Eligible W i ↔
      Disjoint (Automata.upperRun (signed c Γ) (seedName (q i) (m i)) (W i))
          (forbiddenPredecessors c Γ) ∧
      exclusion (q i) (m i) (W i) ∉ leastClosure c Γ ∧
        flipC (seed (q i) (m i) (W i)) ∉ leastClosure c Γ := by sorry
