-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_concavification_le_majorant
-- name    : BayesianPersuasion.Proof.concavification_le_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:05.528006+00:00
-- url     : https://prove2.me/theorems/285fd07e-ab5c-4004-aa51-51e9285c1df7
-- title:
--   Proof: concavification le majorant
-- statement:
--   The Proof construction uses the concavification le majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L202-L215
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L202-L215

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

theorem BayesianPersuasion.Proof.concavification_le_majorant (g : (Ω → ℝ) → ℝ)
    (hg : ConcaveOn ℝ (probabilitySimplex Ω) g)
    (hmajor : ∀ p : Belief Ω, senderPayoff u v p ≤ g p.val) (p : Belief Ω) :
    concavification u v p.val ≤ g p.val := by sorry
