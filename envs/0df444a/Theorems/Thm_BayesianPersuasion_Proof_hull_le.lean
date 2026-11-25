-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_hull_le
-- name    : BayesianPersuasion.Proof.hull_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:03:43.906098+00:00
-- url     : https://prove2.me/theorems/1c8b88f0-ff0c-4041-9abb-81182aac213b
-- title:
--   Proof: hull le
-- statement:
--   The Proof construction uses the hull le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L96-L99
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L96-L99

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

theorem BayesianPersuasion.Proof.hull_le (p : Belief Ω) {z : ℝ}
    (hz : (p.val, z) ∈ convexHull ℝ (bestReplyPayoffs u v)) :
    z ≤ concavification u v p.val := by sorry
