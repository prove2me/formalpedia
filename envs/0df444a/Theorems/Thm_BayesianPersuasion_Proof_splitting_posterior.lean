-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_splitting_posterior
-- name    : BayesianPersuasion.Proof.splitting_posterior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:01:22.545721+00:00
-- url     : https://prove2.me/theorems/193573ce-3604-4a2b-885f-8c662a4be268
-- title:
--   Proof: splitting posterior
-- statement:
--   The Proof construction uses the splitting posterior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L130-L139
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L130-L139

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

theorem BayesianPersuasion.Proof.splitting_posterior (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b)
    (s : Fin n) (hs : w.val s ≠ 0) :
    signalPosterior p (splittingSignal p hp w b hb) s = b s := by sorry
