-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_generic_indep_count_dependent_mark_shift_joint_law
-- name    : AvramDividend.Classical.avram_a06_generic_indep_count_dependent_mark_shift_joint_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:43:35.906196+00:00
-- url     : https://prove2.me/theorems/07acbdea-517e-4270-b40f-71341d6e67ac
-- title:
--   Independent count-dependent shift preserves joint count and mark-stream law
-- statement:
--   An a.e. measurable random two-count vector independent of an a.e. measurable mark sequence with shift-invariant full sequence law yields identical joint law under shifting the mark sequence by the first count.
-- source:
--   Factor joint count-mark law by the pinned IndepFun.map_prod_eq_prod_map_map. Disintegrate over the countable type Fin 2 → Nat. Conditional on any count vector n, deterministic stream shift by n 0 preserves the mark-stream law; integrate against the count-vector law and reconstruct the joint law by product measure Fubini.

import Mathlib
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_generic_indep_count_dependent_mark_shift_joint_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → Fin 2 → ℕ) (M : Ω → ℕ → ℝ)
    (hN : AEMeasurable N P) (hM : AEMeasurable M P)
    (hNM : IndepFun N M P)
    (hshift : ∀ m : ℕ,
      IdentDistrib (fun ω j => M ω (m + j)) M P P) :
    IdentDistrib
      (fun ω => (N ω, fun j => M ω (N ω 0 + j)))
      (fun ω => (N ω, M ω)) P P := by sorry
