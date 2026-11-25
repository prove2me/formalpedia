-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_persuasion_gain_iff
-- name    : BayesianPersuasion.Proof.persuasion_gain_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:05:57.611815+00:00
-- url     : https://prove2.me/theorems/5b976122-2df0-4b02-b268-9e36f4d31c76
-- title:
--   Proof: persuasion gain iff
-- statement:
--   The Proof construction uses the persuasion gain iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L228-L237
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L228-L237

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

theorem BayesianPersuasion.Proof.persuasion_gain_iff (p : Belief Ω) (hp : FullSupport p) :
    (∃ (n : ℕ) (π : Signal Ω n), senderPayoff u v p < signalValue u v p π) ↔
      senderPayoff u v p < concavification u v p.val := by sorry
