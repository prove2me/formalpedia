-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_senderPreferred_exists
-- name    : BayesianPersuasion.Proof.senderPreferred_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:57:47.06612+00:00
-- url     : https://prove2.me/theorems/1ed42ec4-0feb-470e-9dd5-7afcccc80e0e
-- title:
--   Proof: sender Preferred exists
-- statement:
--   The Proof construction uses the sender Preferred exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L82-L89
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L82-L89

module
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BayesianPersuasion_Primitives
set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable (Ω : Type uΩ) [Fintype Ω]
variable {Ω} {A : Type uA}
open BayesianPersuasion.Proof
variable [TopologicalSpace A]
variable [CompactSpace A] [Nonempty A]

theorem BayesianPersuasion.Proof.senderPreferred_exists (u v : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) (p : Belief Ω) :
    ∃ a, SenderPreferred u v p a := by sorry
