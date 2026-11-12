-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_single_random_mark_interval_product_law_20261111
-- name    : AvramDividend.Classical.avram_a06_single_random_mark_interval_product_law_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:38:44.496391+00:00
-- url     : https://prove2.me/theorems/20c4ebba-ea79-4a92-b36b-f0e0dfa332da
-- title:
--   Single random marked interval law factors as product count-mark pushforward
-- statement:
--   The exact one-dimensional analogue of the Proved random marked-grid pushforward product law. By independence of the full count grid and mark sequence and measurability of their variable bounded interval sum, the single interval law is the pushforward of the product marginal measure. This is a direct prerequisite for applying product-measure characteristic-function Fubini.

import Mathlib
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_single_random_mark_interval_product_law_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P)
    (i : Fin n) :
    Measure.map (fun ω : Ω =>
      ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P =
    Measure.map (fun p : (Fin (n + 1) → ℕ) × (ℕ → ℝ) =>
      ∑ j ∈ Finset.Ico (p.1 i.castSucc) (p.1 i.succ), p.2 j)
      ((Measure.map (fun ω => fun k => N k ω) P).prod
        (Measure.map (fun ω => fun k => Y k ω) P)) := by sorry
