-- Prove2me | Theorems.Thm_DeciSigma1_Full_Logic_holds_eq_iff
-- name    : DeciSigma1.Full.Logic.holds_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:18:26.143047+00:00
-- url     : https://prove2.me/theorems/29b6eb82-ea92-4f8f-85df-e6f97936cf7b
-- title:
--   Logic: holds eq iff
-- statement:
--   An equation holds exactly when both sides have the same value.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Logic.lean#L174-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Logic.lean#L174-L178

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Logic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Logic
open DeciSigma1.Constraints DeciSigma1.Semantics DeciSigma1.Full.Models
variable {n : ℕ} {V W : Type}
variable (c : Fin n → Bool)

theorem DeciSigma1.Full.Logic.holds_eq_iff (ρ : V → Tree n) (s t : Term n V) :
    (DeciSigma1.Logic.QuantifierFreeFormula.eq s t).Holds (interpretation c) ρ ↔
      s.eval ρ = t.eval ρ := by sorry
