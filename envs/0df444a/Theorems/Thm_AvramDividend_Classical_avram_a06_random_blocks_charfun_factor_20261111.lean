-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_random_blocks_charfun_factor_20261111
-- name    : AvramDividend.Classical.avram_a06_random_blocks_charfun_factor_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:27:02.706545+00:00
-- url     : https://prove2.me/theorems/23364f73-e520-4d65-b44c-cf5d571a7141
-- title:
--   Joint characteristic function of random disjoint IID mark blocks factors from independent count increments
-- statement:
--   Given an everywhere nondecreasing measurable count grid, independent count increments, an IID mark stream, and independence of the entire count vector from the entire mark stream, the joint characteristic function of successive disjoint random-length mark sums equals the product of their marginal characteristic functions. The proof obligation is the conditional finite-block mark factorisation followed by mixing over independent count increments. This theorem is the exact analytic bridge for the parent random-block independence theorem 000dffc9 and preserves the original probability space and mark indices.

import Mathlib
open MeasureTheory Set ProbabilityTheory Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_random_blocks_charfun_factor_20261111
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
    ∀ t : WithLp 2 (Fin n → ℝ),
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
        ∏ i : Fin n, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P)
          (t.ofLp i) := by sorry
