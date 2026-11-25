-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_bounded
-- name    : BayesianPersuasion.Proof.senderPayoff_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:01.32594+00:00
-- url     : https://prove2.me/theorems/c32279b9-39cd-440e-907b-068694d5fca9
-- title:
--   Proof: sender Payoff bounded
-- statement:
--   The Proof construction uses the sender Payoff bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L217-L226
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L217-L226

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
variable [TopologicalSpace A] [CompactSpace A] [Nonempty A] [T2Space A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))
include hu hv

theorem BayesianPersuasion.Proof.senderPayoff_bounded :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : Belief Ω, |senderPayoff u v p| ≤ M := by sorry
