-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_random_disjoint_iid_mark_sums_independent
-- name    : AvramDividend.Classical.avram_a06_random_disjoint_iid_mark_sums_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:41:45.904666+00:00
-- url     : https://prove2.me/theorems/000dffc9-98b4-40d9-bed3-686ab3d57574
-- title:
--   Independent random count differences and IID marks yield independent disjoint random-length marked sums
-- statement:
--   If a finite monotone random count vector has independent consecutive count differences, and the full count vector is independent of an IID identically distributed mark stream, then mark sums over its successive random disjoint index blocks are jointly independent. Conditional on the count vector, disjoint mark blocks are independent and their laws depend only on the corresponding count differences; independence of the differences gives the joint product law. This isolates the generic random-index-mark probability step from the A06 original exponential renewal count independent-increments construction. A separate formal bridge into target 2a80927e is still required.

import Mathlib
open MeasureTheory Set ProbabilityTheory Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_random_disjoint_iid_mark_sums_independent
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hNmono : ∀ ω, Monotone (fun i => N i ω))
    (hCount : iIndepFun (fun (i : Fin n) ω =>
      N i.succ ω - N i.castSucc ω) P)
    (hMarks : iIndepFun Y P)
    (hSameLaw : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P) :
    iIndepFun (fun (i : Fin n) ω =>
      ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P := by sorry
