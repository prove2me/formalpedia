-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_compile_runPrefix
-- name    : DeciSigma1.Full.Reduction.compile_runPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:16:14.211802+00:00
-- url     : https://prove2.me/theorems/7d80aff5-d908-4b7f-991c-8b9f7ad822ff
-- title:
--   Reduction: compile run Prefix
-- statement:
--   The Reduction construction uses the compile run Prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L145-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L145-L151

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

theorem DeciSigma1.Full.Reduction.compile_runPrefix (c : Fin n → Bool) (Γ : List (LitT n V)) (q : Fin k → V × V)
    (m : Fin k → Bool) (W : Fin k → List (Fin n)) (i : Fin k) {a : ℕ}
    (h : (compile c Γ q m).runPrefix W i a ≠ none) :
    (compile c Γ q m).runPrefix W i a =
      some (Automata.upperRun (signed c Γ) (seedName (q i) (m i)) ((W i).take a),
          Automata.lowerRun (signed c Γ) (exclusionName (q i) (m i)) ((W i).take a)) := by sorry
