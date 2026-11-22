-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_seed_cone_regular
-- name    : DeciSigma1.Full.Reduction.seed_cone_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:11:16.459216+00:00
-- url     : https://prove2.me/theorems/ca4d4c7f-84f7-484d-8b04-67dfea2e6de9
-- title:
--   Reduction: seed cone regular
-- statement:
--   For a seed without a unary obstruction and every signed variable, the set of paths at which
--   the seed derives the variable is regular.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L319-L341
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L319-L341

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

theorem DeciSigma1.Full.Reduction.seed_cone_regular (a : Closure.Config n V)
    (ha : ¬ HasUnaryObstruction c Γ (a.1, a.2.1) a.2.2) (q : V × Bool) :
    IsRegular {t | Reach c Γ a (q.1, q.2, t)} := by sorry
