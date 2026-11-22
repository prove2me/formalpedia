-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_flip_inter_symm
-- name    : DeciSigma1.Full.Closure.flip_inter_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:07:07.372559+00:00
-- url     : https://prove2.me/theorems/83c58ea2-0c4c-4fbb-a07c-79135c46e9c5
-- title:
--   Closure: flip inter symm
-- statement:
--   `A` meets the sign exchange of `B` exactly when `B` meets the sign exchange of `A`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L457-L465
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L457-L465

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_map

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Automata
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (Γ : List (LitT n V))
variable {c Γ}
variable (c Γ)
variable {c Γ}
omit [Fintype V]

theorem DeciSigma1.Full.Closure.flip_inter_symm {A B : Finset (V × Bool)} :
    (A ∩ B.map flipEmb).Nonempty ↔ (B ∩ A.map flipEmb).Nonempty := by sorry
