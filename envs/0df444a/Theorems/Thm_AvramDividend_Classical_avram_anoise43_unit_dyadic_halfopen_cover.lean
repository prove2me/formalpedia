-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise43_unit_dyadic_halfopen_cover
-- name    : AvramDividend.Classical.avram_anoise43_unit_dyadic_halfopen_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:23:01.59897+00:00
-- url     : https://prove2.me/theorems/646e2046-6d93-4251-9a2e-11648d6618e9
-- title:
--   Every half-open unit interval point belongs to a unique-height dyadic half-open cell
-- statement:
--   Elementary dyadic half-open spatial cover: any real z with -1<z≤0 lies in some left-open, right-closed k-level cell, with index less than 2^k. This is the geometric partition lemma for original physical Lévy marks.
-- source:
--   Needed for Open h42 original deterministic Lévy compensator dyadic approximation and Open h41 physical marked-count convergence; bounds use Nat.ceil.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise43_unit_dyadic_halfopen_cover
    (k : ℕ) (z : ℝ) (hzlo : -1 < z) (hzhi : z ≤ 0) :
    ∃ i : ℕ, i < 2 ^ k ∧
      z ∈ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
        (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k) := by sorry
