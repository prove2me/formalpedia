-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_seedConsistency_iff_terminalRootConditions
-- name    : DeciSigma1.Full.Reduction.seedConsistency_iff_terminalRootConditions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:11:02.865991+00:00
-- url     : https://prove2.me/theorems/9838be38-aa43-4f17-bd9b-91347222a7c1
-- title:
--   Reduction: seed Consistency iff terminal Root Conditions
-- statement:
--   `SeedConsistency` and `TerminalRootConditions` are equivalent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L258-L277
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L258-L277

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Automata
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Reduction.seedConsistency_iff_terminalRootConditions (A B : Fin k → Closure.Config n V) :
    SeedConsistency c Γ A B ↔ TerminalRootConditions c Γ A B := by sorry
