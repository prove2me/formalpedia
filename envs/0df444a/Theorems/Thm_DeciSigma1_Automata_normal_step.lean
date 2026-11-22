-- Prove2me | Theorems.Thm_DeciSigma1_Automata_normal_step
-- name    : DeciSigma1.Automata.normal_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:19.392051+00:00
-- url     : https://prove2.me/theorems/e035a312-276f-4349-aea8-7c1e531c3709
-- title:
--   Automata: normal step
-- statement:
--   The Automata construction uses the normal step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L312-L332
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L312-L332

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem DeciSigma1.Automata.normal_step {Γ : List (LitT n V)} {x y z : V} {u t w : List (Fin n)}
    (h : Normal Γ x u y t) (hm : Move Γ (y, t) (z, w)) : Normal Γ x u z w := by sorry
