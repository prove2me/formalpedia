-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_sum_pad
-- name    : BayesianPersuasion.Proof.sum_pad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:06:06.492796+00:00
-- url     : https://prove2.me/theorems/98d25aa5-97fb-469d-babc-20543072b158
-- title:
--   Proof: sum pad
-- statement:
--   Summation is unaffected by padding with zero coefficients.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/CompactHull.lean#L40-L54
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/CompactHull.lean#L40-L54

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

theorem BayesianPersuasion.Proof.sum_pad {k N : ℕ} (hk : k ≤ N) {G : Type*} [AddCommMonoid G]
    (f : Fin k → G) :
    (∑ j : Fin N, if h : j.val < k then f ⟨j.val, h⟩ else 0) = ∑ j, f j := by sorry
