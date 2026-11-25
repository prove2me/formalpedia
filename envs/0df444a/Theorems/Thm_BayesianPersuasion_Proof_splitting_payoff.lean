-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_splitting_payoff
-- name    : BayesianPersuasion.Proof.splitting_payoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:00:53.916798+00:00
-- url     : https://prove2.me/theorems/1bf50d35-5f5b-47fb-82c1-1ec3c9856973
-- title:
--   Proof: splitting payoff
-- statement:
--   The Proof construction uses the splitting payoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L141-L151
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L141-L151

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

theorem BayesianPersuasion.Proof.splitting_payoff (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b)
    (f : Belief Ω → ℝ) :
    ∑ s, signalMass p (splittingSignal p hp w b hb) s *
      f (signalPosterior p (splittingSignal p hp w b hb) s) = ∑ s, w.val s * f (b s) := by sorry
