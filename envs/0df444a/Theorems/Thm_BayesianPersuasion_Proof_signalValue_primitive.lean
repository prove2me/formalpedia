-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_signalValue_primitive
-- name    : BayesianPersuasion.Proof.signalValue_primitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:45.678407+00:00
-- url     : https://prove2.me/theorems/23e4bef7-6081-47cb-bb74-de0e1d2a47f7
-- title:
--   Proof: signal Value primitive
-- statement:
--   The posterior payoff formula is the state/message expectation of the
--   sender's primitive utility under any sender-preferred receiver actions.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L39-L57
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L39-L57

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]
open BayesianPersuasion.Proof

theorem BayesianPersuasion.Proof.signalValue_primitive [TopologicalSpace A] [CompactSpace A] [Nonempty A]
    (u v : A → Ω → ℝ) (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) (p : Belief Ω) {n : ℕ}
    (π : Signal Ω n) (a : Fin n → A)
    (ha : ∀ s, SenderPreferred u v (signalPosterior p π s) (a s)) :
    signalValue u v p π = ∑ ω, p.val ω * ∑ s, (π ω).val s * v (a s) ω := by sorry
