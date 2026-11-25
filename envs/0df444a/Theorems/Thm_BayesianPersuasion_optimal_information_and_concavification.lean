-- Prove2me | Theorems.Thm_BayesianPersuasion_optimal_information_and_concavification
-- name    : BayesianPersuasion.optimal_information_and_concavification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:08:05.712214+00:00
-- url     : https://prove2.me/theorems/c14e7324-a6cf-4a7c-8c6b-6832c860b40b
-- title:
--   Bayesian Persuasion: optimal information and concavification
-- statement:
--   An optimal finite signal exists and its value is the least concave
--   majorant of the economically derived sender payoff on the entire simplex.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Theorems.lean#L65-L75
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Theorems.lean#L65-L75

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

theorem BayesianPersuasion.optimal_information_and_concavification (p : Belief Ω) (hp : FullSupport p) :
    (∃ (k : ℕ) (_ : k ≤ Fintype.card Ω + 2) (π : Signal Ω k),
      signalValue u v p π = concavification u v p.val ∧
      ∀ (m : ℕ) (σ : Signal Ω m), signalValue u v p σ ≤ signalValue u v p π) ∧
    ConcaveOn ℝ (probabilitySimplex Ω) (concavification u v) ∧
    (∀ q : Belief Ω, senderPayoff u v q ≤ concavification u v q.val) ∧
    (∀ g : (Ω → ℝ) → ℝ, ConcaveOn ℝ (probabilitySimplex Ω) g →
      (∀ q : Belief Ω, senderPayoff u v q ≤ g q.val) →
      ∀ q : Belief Ω, concavification u v q.val ≤ g q.val) := by sorry
