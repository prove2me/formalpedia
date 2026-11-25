-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_splitting_joint
-- name    : BayesianPersuasion.Proof.splitting_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:00:41.073631+00:00
-- url     : https://prove2.me/theorems/dc83cb00-fa5b-52e2-adfa-75cec137d8ac
-- title:
--   Proof: splitting joint
-- statement:
--   The Proof construction uses the splitting joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L117-L122
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L117-L122

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

theorem BayesianPersuasion.Proof.splitting_joint (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b)
    (ω : Ω) (s : Fin n) :
    p.val ω * (splittingSignal p hp w b hb ω).val s = w.val s * (b s).val ω := by sorry
