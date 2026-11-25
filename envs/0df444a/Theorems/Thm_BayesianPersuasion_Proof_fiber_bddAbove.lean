-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_fiber_bddAbove
-- name    : BayesianPersuasion.Proof.fiber_bddAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:06:20.020717+00:00
-- url     : https://prove2.me/theorems/e9a010ae-89a1-4a95-bc4f-df24ef2f7ed1
-- title:
--   Proof: fiber bdd Above
-- statement:
--   The Proof construction uses the fiber bdd Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L90-L94
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L90-L94

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

theorem BayesianPersuasion.Proof.fiber_bddAbove (p : Belief Ω) :
    BddAbove {z | (p.val, z) ∈ convexHull ℝ (bestReplyPayoffs u v)} := by sorry
