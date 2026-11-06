-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_same_window_mark_simple_L2_martingale
-- name    : AvramDividend.Classical.avram_p4_s3_interval_e_original_same_window_mark_simple_L2_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:53:56.257207+00:00
-- url     : https://prove2.me/theorems/7726d7c7-ab77-4629-8780-8176b764940b
-- title:
--   Finite same-window original negative-mark simple predictable integrals are L2 martingale-centred
-- statement:
--   For arbitrary finite sets of negative Borel mark cells on the same original physical time window, and uniformly bounded starting-filtration-predictable L² coefficients, the finite sum of actual compensated marked jump counts lies in L² and has exact conditional expectation zero given the original starting filtration. This extends one physical finite-band cell to all finite mark-simple integrands without assuming disjoint bands, Poisson isometry, a new stochastic axiom or equality in law.
-- source:
--   Source-exact composition of public Proved 11dd20c2 physical weighted negative-band L2 martingale per mark cell with pinned Mathlib memLp_finset_sum and condExp_finset_sum. Preserves physical original Lévy count on same time interval and conditioning at F_s.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_e_original_same_window_mark_simple_L2_martingale
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ι → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : ι → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 s] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (F : Finset ι) :
    let Z : ι → Ω → ℝ := fun i ω =>
      H i ω * (((((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i)).toReal) -
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    MemLp (∑ i ∈ F, Z i) 2 P ∧
    P[(∑ i ∈ F, Z i) | 𝓕 s] =ᵐ[P] (0 : Ω → ℝ) := by sorry
