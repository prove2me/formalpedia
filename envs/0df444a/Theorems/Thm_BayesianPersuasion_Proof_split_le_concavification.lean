-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_split_le_concavification
-- name    : BayesianPersuasion.Proof.split_le_concavification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:03:45.621949+00:00
-- url     : https://prove2.me/theorems/0c198013-c952-40bf-bb93-fcf69c861bda
-- title:
--   Proof: split le concavification
-- statement:
--   The Proof construction uses the split le concavification property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L132-L135
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L132-L135

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

theorem BayesianPersuasion.Proof.split_le_concavification (p : Belief Ω) {n : ℕ} (w : Belief (Fin n))
    (b : Fin n → Belief Ω) (hb : BayesPlausible p w b) :
    splitValue u v w b ≤ concavification u v p.val := by sorry
