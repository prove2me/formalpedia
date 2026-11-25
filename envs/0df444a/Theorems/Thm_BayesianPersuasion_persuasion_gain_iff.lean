-- Prove2me | Theorems.Thm_BayesianPersuasion_persuasion_gain_iff
-- name    : BayesianPersuasion.persuasion_gain_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:16:13.65579+00:00
-- url     : https://prove2.me/theorems/849601d1-3962-47c8-b476-6c72bddcf9f0
-- title:
--   Bayesian Persuasion: persuasion gain iff
-- statement:
--   Strict persuasion gain is exactly the concavification gap above the
--   sender's payoff at the uninformed common prior.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Theorems.lean#L80-L83
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Theorems.lean#L80-L83

module
public import Definitions.Def_BayesianPersuasion_Attainment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Definitions.Def_BayesianPersuasion_Theorems
public import Theorems.Thm_BayesianPersuasion_Proof_persuasion_gain_iff

set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω] [Nonempty Ω]
variable [MetricSpace A] [CompactSpace A] [Nonempty A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))
include hu hv

theorem BayesianPersuasion.persuasion_gain_iff (p : Belief Ω) (hp : FullSupport p) :
    (∃ (n : ℕ) (π : Signal Ω n), senderPayoff u v p < signalValue u v p π) ↔
      senderPayoff u v p < concavification u v p.val := by sorry
