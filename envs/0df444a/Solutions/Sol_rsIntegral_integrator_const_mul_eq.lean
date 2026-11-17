-- Prove2me | solution 1 for rsIntegral_integrator_const_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:28:24.608652+00:00
-- url     : https://prove2.me/submissions/0f20865f-a712-46ee-98cf-4a5a45ef41a7

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Tactic
import Theorems.Thm_taggedCommonLimit_unique
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
open Finset Set
noncomputable section

/-- The source integrability witness for a nonnegative scalar integrator. -/
private theorem rsIntegrable_integrator_const_mul {f α : ℝ → ℝ} {a b k : ℝ}
    (hk : 0 ≤ k) (h : RSIntegrable f α a b) :
    RSIntegrable f (fun x => k * α x) a b :=
  ⟨rsIntegralWitness_integrator_const_mul hk h⟩

theorem solution {f α : ℝ → ℝ} {a b k : ℝ}
    (hk : 0 ≤ k) (h : RSIntegrable f α a b) :
    rsIntegral f (fun x => k * α x) a b (rsIntegrable_integrator_const_mul hk h) =
      k * rsIntegral f α a b h := by
  -- We prove equality by invoking the uniqueness of the tagged limits!
  exact taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrator_const_mul hk h))
    (taggedCommonLimit_integrator_const_mul hk (rsIntegral_spec h))
