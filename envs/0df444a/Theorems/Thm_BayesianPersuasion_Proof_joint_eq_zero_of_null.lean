-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_joint_eq_zero_of_null
-- name    : BayesianPersuasion.Proof.joint_eq_zero_of_null
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:06:01.97121+00:00
-- url     : https://prove2.me/theorems/178a9d72-91bc-4380-987e-3433ecb77487
-- title:
--   Proof: joint eq zero of null
-- statement:
--   The Proof construction uses the joint eq zero of null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L52-L58
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L52-L58

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_Signals
set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} [Fintype Ω]
open BayesianPersuasion.Proof

theorem BayesianPersuasion.Proof.joint_eq_zero_of_null (p : Belief Ω) {n : ℕ} (π : Signal Ω n)
    (s : Fin n) (hs : signalMass p π s = 0) (ω : Ω) : p.val ω * (π ω).val s = 0 := by sorry
