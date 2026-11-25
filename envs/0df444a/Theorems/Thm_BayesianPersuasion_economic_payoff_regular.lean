-- Prove2me | Theorems.Thm_BayesianPersuasion_economic_payoff_regular
-- name    : BayesianPersuasion.economic_payoff_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:08:13.137411+00:00
-- url     : https://prove2.me/theorems/cd674533-6e14-4c62-a819-6a118a3d79d4
-- title:
--   Bayesian Persuasion: economic payoff regular
-- statement:
--   The receiver optimization and sender tie rule produce a bounded USC payoff.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Theorems.lean#L32-L40
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Theorems.lean#L32-L40

module
public import Definitions.Def_BayesianPersuasion_Attainment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Definitions.Def_BayesianPersuasion_Theorems
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

theorem BayesianPersuasion.economic_payoff_regular :
    (∀ p : Belief Ω, ∃ a, SenderPreferred u v p a ∧ senderPayoff u v p = expected v p a) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ p : Belief Ω, |senderPayoff u v p| ≤ M) ∧
    UpperSemicontinuous (senderPayoff u v) := by sorry
