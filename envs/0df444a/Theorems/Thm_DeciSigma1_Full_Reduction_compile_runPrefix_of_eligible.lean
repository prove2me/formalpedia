-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_compile_runPrefix_of_eligible
-- name    : DeciSigma1.Full.Reduction.compile_runPrefix_of_eligible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:16:26.776314+00:00
-- url     : https://prove2.me/theorems/4423c4f8-b7e8-4354-8a60-79eec41c92cf
-- title:
--   Reduction: compile run Prefix of eligible
-- statement:
--   The Reduction construction uses the compile run Prefix of eligible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L179-L184
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L179-L184

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

theorem DeciSigma1.Full.Reduction.compile_runPrefix_of_eligible {W : Fin k → List (Fin n)} {i : Fin k}
    (h : (compile c Γ q m).Eligible W i) (a : Nat) :
    (compile c Γ q m).runPrefix W i a =
      some (Automata.upperRun (signed c Γ) (seedName (q i) (m i)) ((W i).take a),
        Automata.lowerRun (signed c Γ) (exclusionName (q i) (m i)) ((W i).take a)) := by sorry
