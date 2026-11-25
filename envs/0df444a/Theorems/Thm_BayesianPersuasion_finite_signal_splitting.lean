-- Prove2me | Theorems.Thm_BayesianPersuasion_finite_signal_splitting
-- name    : BayesianPersuasion.finite_signal_splitting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:08:01.646203+00:00
-- url     : https://prove2.me/theorems/442e3f76-4018-5b5d-8fbb-768974508977
-- title:
--   Bayesian Persuasion: finite signal splitting
-- statement:
--   Finite Bayes-plausible splittings are exactly finite state-conditional
--   experiments at a full-support prior, with honest posterior recovery restricted to nonnull messages.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Theorems.lean#L44-L60
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Theorems.lean#L44-L60

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

theorem BayesianPersuasion.finite_signal_splitting (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) :
    BayesPlausible p w b ↔ ∃ π : Signal Ω n,
      (∀ s ω, p.val ω * (π ω).val s = w.val s * (b s).val ω) ∧
      (∀ s, w.val s ≠ 0 → signalPosterior p π s = b s) ∧
      signalValue u v p π = splitValue u v w b := by sorry
