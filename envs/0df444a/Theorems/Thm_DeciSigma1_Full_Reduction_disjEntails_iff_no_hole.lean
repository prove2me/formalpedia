-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_disjEntails_iff_no_hole
-- name    : DeciSigma1.Full.Reduction.disjEntails_iff_no_hole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:17:34.277507+00:00
-- url     : https://prove2.me/theorems/f7d66757-ae7f-4118-ab55-4cf59d4fac93
-- title:
--   Reduction: disj Entails iff no hole
-- statement:
--   For a satisfiable constraint, the disjunctive entailment holds exactly when the reader of no
--   mode has a hole.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L313-L317
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L313-L317

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)} {q : Fin k → V × V}

theorem DeciSigma1.Full.Reduction.disjEntails_iff_no_hole (hs : ∃ ρ, SatT c ρ Γ) :
    DisjEntailsIn (fun _ => True) c Γ q ↔
      ¬ ∃ m : Fin k → Bool, ∃ W, (compile c Γ q m).IsHole W := by sorry
