-- Prove2me | solution 1 for exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:13:35.37139+00:00
-- url     : https://prove2.me/submissions/a1e49736-3130-4f8e-88e4-0ac5ad895cc4

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_continuous_eval_divByMonic_X_sub_C
import Theorems.Thm_SmoothJordanDomain_isCompact_frontier


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ xi ∈ frontier Omega.carrier,
      ∀ sigma ∈ frontier Omega.carrier,
        ‖Polynomial.eval sigma
          (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤ Q := by
  let f : ℂ × ℂ → ℝ := fun x =>
    ‖Polynomial.eval x.2
      (p /ₘ (Polynomial.X - Polynomial.C x.1))‖
  have hf : Continuous f :=
    (continuous_eval_divByMonic_X_sub_C p).norm
  have hnonempty :
      (frontier Omega.carrier ×ˢ frontier Omega.carrier).Nonempty := by
    refine ⟨(Omega.boundaryParam 0, Omega.boundaryParam 0), ?_, ?_⟩ <;>
      rw [← Omega.boundaryParam_range] <;> exact mem_range_self 0
  obtain ⟨x, hx, hmax⟩ :=
    (Omega.isCompact_frontier.prod Omega.isCompact_frontier).exists_isMaxOn
      hnonempty hf.continuousOn
  refine ⟨f x, norm_nonneg _, ?_⟩
  intro xi hxi sigma hsigma
  have hpair : (xi, sigma) ∈
      frontier Omega.carrier ×ˢ frontier Omega.carrier := ⟨hxi, hsigma⟩
  exact hmax hpair
