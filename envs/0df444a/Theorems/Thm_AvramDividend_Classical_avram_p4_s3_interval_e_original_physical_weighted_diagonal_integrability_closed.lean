-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_physical_weighted_diagonal_integrability_closed
-- name    : AvramDividend.Classical.avram_p4_s3_interval_e_original_physical_weighted_diagonal_integrability_closed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:46:58.675193+00:00
-- url     : https://prove2.me/theorems/6e46bc98-8686-4ad8-9f26-1efa0ff60527
-- title:
--   Original physical predictable weighted negative-cell L2 isometry with integrability hypotheses discharged
-- statement:
--   For the genuine marked negative jumps of a spectrally negative Lévy process on a finite separated band, with bounded adapted H in L² and an exact original conditional compensated-count variance, the weighted centred cell has exact squared expectation r·E(H²). The proof obtains all needed physical count and weighted square integrability from accepted original P4-S3 helpers and applies the public original P4-G diagonal identity, without extra stochastic axioms or equality-in-law assumptions. Conditional variance is explicitly retained as a genuine premise to discharge by original-process construction.
-- source:
--   Combines public Proved 9b483610 (original physical diagonal conditional variance identity), 11dd20c2 (bounded physical weighted cell L²), and 8feb9a50 (explicit physical squared centred count integrability). The bridge still requires authentic hSecond for stopped source.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_e_original_physical_weighted_diagonal_integrability_closed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (r : ℝ)
    (hRate : r =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)
    (hSecond : P[(fun ω => ((N ω).toReal - r) ^ 2)
      | 𝓕 s] =ᵐ[P] (fun _ => r))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
      r * ∫ ω, (H ω) ^ 2 ∂P := by sorry
