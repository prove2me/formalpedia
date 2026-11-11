-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise46_finite_dyadic_mark_endpoint_weighted_convergence
-- name    : AvramDividend.Classical.avram_anoise46_finite_dyadic_mark_endpoint_weighted_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:48:45.363984+00:00
-- url     : https://prove2.me/theorems/8436d2ce-6e55-465f-95db-4e28d9f7d23a
-- title:
--   Finite marked dyadic endpoint weighted cardinal sums converge to signed marks
-- statement:
--   For any finite set of marks in B, half-open dyadic cell endpoint weights times each cell's cardinality converge to the exact real signed sum of marks. This is a finite deterministic inequality consequence of dyadic covering and the per-mark error of at most 2^-k.
-- source:
--   Necessary deterministic half of root-connected Open h41, using existing Proved h34 and h43; independent of all stochastic assumptions and measure integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise46_finite_dyadic_mark_endpoint_weighted_convergence
    {α : Type*} [DecidableEq α] (n : ℕ) (F : Finset α)
    (j : α → ℝ)
    (hF : ∀ u ∈ F, j u ∈ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) :
    Tendsto
      (fun k : ℕ => ∑ i ∈ Finset.range (2 ^ k),
        (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
          ((F.filter (fun u => j u ∈
            (Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))) ∩
              Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
                (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)))).card : ℝ))
      atTop (𝓝 (∑ u ∈ F, j u)) := by sorry
