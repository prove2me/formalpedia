-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero
-- name    : AvramDividend.Classical.avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:57:07.524523+00:00
-- url     : https://prove2.me/theorems/41f9c067-9577-4f1a-b0da-d33bbe46392c
-- title:
--   Exact original stopped z-weighted negative-band signed compensated Levy mark mean zero without clock assumptions
-- statement:
--   Source-faithful exact original SpectrallyNegativeLevy physical NX marked jump signed compensator z-integral over (0,τ]×B, where B is a finite separated negative reciprocal band, is integrable and centred at ANY right-continuous stopping time bounded by T with countable range. No global negative jump activity assumption, no synthetic point process, no independent stochastic martingale assumption, no auxiliary integrability or regularity hypotheses on τ. Reuse the directly source-proved L1 physical finite-band stopped z-mark result with its one automatic stopping-clock integrability premise, discharged by the independently remote-Proved theorem that bounded right-continuous stopping-time clocks have integrable real parts. Exact random clock, physical Nx, signed mark z and Levy ν compensator are preserved. This completes the finite separated negative-band true stopped-mark component for Avram stopped Ito-Meyer source work.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (a b : ℕ) (hab : a ≤ b)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτbound : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable)
    :
    let B : Set ℝ :=
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let J : Ω → ℝ := fun ω =>
      (∫ p in Ioc 0 (τ ω).untopA ×ˢ B, p.2 ∂NX ω) -
        (((τ ω).untopA : ℝ) * (∫ z in B, z ∂X.ν))
    Integrable J P ∧ (∫ ω, J ω ∂P) = 0 := by sorry
