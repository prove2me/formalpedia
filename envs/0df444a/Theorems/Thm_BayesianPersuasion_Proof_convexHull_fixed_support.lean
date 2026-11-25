-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_convexHull_fixed_support
-- name    : BayesianPersuasion.Proof.convexHull_fixed_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:05:58.783846+00:00
-- url     : https://prove2.me/theorems/4674b178-d7b8-483b-aede-efa92ba54f08
-- title:
--   Proof: convex Hull fixed support
-- statement:
--   The Proof construction uses the convex Hull fixed support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/CompactHull.lean#L56-L76
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/CompactHull.lean#L56-L76

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_CompactHull
set_option autoImplicit true
@[expose] public section
public section
open Set Finset
open BayesianPersuasion BayesianPersuasion.Proof
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem BayesianPersuasion.Proof.convexHull_fixed_support {s : Set E} (hs : s.Nonempty) {x : E}
    (hx : x ∈ convexHull ℝ s) :
    ∃ (w : Belief (Fin (Module.finrank ℝ E + 1)))
      (z : Fin (Module.finrank ℝ E + 1) → s), ∑ j, w.val j • (z j).val = x := by sorry
