-- Prove2me | solution 1 for rsIntegrable_integrator_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:38:57.840644+00:00
-- url     : https://prove2.me/submissions/30f70072-6908-454a-b420-ece34325e28d

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
open Finset
open Set
noncomputable section
section Thm_1_3_helper
end Thm_1_3_helper
section Theorem_1_3
end Theorem_1_3
section integrator_scalar_multiply

theorem solution {f α : ℝ → ℝ} {a b k : ℝ}
    (hk : 0 ≤ k) (h : RSIntegrable f α a b) :
    RSIntegrable f (fun x => k * α x) a b :=
  ⟨rsIntegralWitness_integrator_const_mul hk h⟩
end integrator_scalar_multiply
end
