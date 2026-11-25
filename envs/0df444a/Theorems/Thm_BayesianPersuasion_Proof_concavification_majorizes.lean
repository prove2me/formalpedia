-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_concavification_majorizes
-- name    : BayesianPersuasion.Proof.concavification_majorizes
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:06:35.136507+00:00
-- url     : https://prove2.me/theorems/bf85a875-0c96-491d-9325-a788fd77abf5
-- title:
--   Proof: concavification majorizes
-- statement:
--   The Proof construction uses the concavification majorizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L186-L188
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L186-L188

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

theorem BayesianPersuasion.Proof.concavification_majorizes (p : Belief Ω) :
    senderPayoff u v p ≤ concavification u v p.val := by sorry
