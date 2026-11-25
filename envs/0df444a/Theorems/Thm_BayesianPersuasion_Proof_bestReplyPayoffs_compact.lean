-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_bestReplyPayoffs_compact
-- name    : BayesianPersuasion.Proof.bestReplyPayoffs_compact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:06:32.280983+00:00
-- url     : https://prove2.me/theorems/597596d5-d265-4f2e-8ce1-aa9b0f9114a9
-- title:
--   Proof: best Reply Payoffs compact
-- statement:
--   The Proof construction uses the best Reply Payoffs compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L78-L80
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L78-L80

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

theorem BayesianPersuasion.Proof.bestReplyPayoffs_compact : IsCompact (bestReplyPayoffs u v) := by sorry
