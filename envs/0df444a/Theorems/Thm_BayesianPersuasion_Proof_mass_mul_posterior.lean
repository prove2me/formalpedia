-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_mass_mul_posterior
-- name    : BayesianPersuasion.Proof.mass_mul_posterior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:00:53.315794+00:00
-- url     : https://prove2.me/theorems/88bfc791-895b-5c05-8b09-202294a1ac23
-- title:
--   Proof: mass mul posterior
-- statement:
--   The Proof construction uses the mass mul posterior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L83-L92
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L83-L92

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

theorem BayesianPersuasion.Proof.mass_mul_posterior (p : Belief Ω) {n : ℕ} (π : Signal Ω n)
    (s : Fin n) (ω : Ω) :
    signalMass p π s * (signalPosterior p π s).val ω = p.val ω * (π ω).val s := by sorry
