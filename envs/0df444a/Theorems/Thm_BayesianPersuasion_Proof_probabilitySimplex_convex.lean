-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_probabilitySimplex_convex
-- name    : BayesianPersuasion.Proof.probabilitySimplex_convex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:06:26.559361+00:00
-- url     : https://prove2.me/theorems/b66d593c-4564-5153-8270-e03837122d41
-- title:
--   Proof: probability Simplex convex
-- statement:
--   The Proof construction uses the probability Simplex convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L177-L184
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L177-L184

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
omit hu hv

theorem BayesianPersuasion.Proof.probabilitySimplex_convex : Convex ℝ (probabilitySimplex Ω) := by sorry
