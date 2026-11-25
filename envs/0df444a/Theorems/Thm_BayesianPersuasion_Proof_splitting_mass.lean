-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_splitting_mass
-- name    : BayesianPersuasion.Proof.splitting_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:01:08.443834+00:00
-- url     : https://prove2.me/theorems/5f7e1264-a610-4f0e-810f-bdbb73431139
-- title:
--   Proof: splitting mass
-- statement:
--   The Proof construction uses the splitting mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L124-L128
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean#L124-L128

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

theorem BayesianPersuasion.Proof.splitting_mass (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b)
    (s : Fin n) : signalMass p (splittingSignal p hp w b hb) s = w.val s := by sorry
