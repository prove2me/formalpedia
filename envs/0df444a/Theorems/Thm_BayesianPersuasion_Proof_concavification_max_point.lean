-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_concavification_max_point
-- name    : BayesianPersuasion.Proof.concavification_max_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:04:06.187639+00:00
-- url     : https://prove2.me/theorems/c8dba301-7ead-54ce-a2bb-ff0b04f3cdc2
-- title:
--   Proof: concavification max point
-- statement:
--   The Proof construction uses the concavification max point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L101-L118
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L101-L118

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

theorem BayesianPersuasion.Proof.concavification_max_point (p : Belief Ω) :
    (p.val, concavification u v p.val) ∈ convexHull ℝ (bestReplyPayoffs u v) := by sorry
