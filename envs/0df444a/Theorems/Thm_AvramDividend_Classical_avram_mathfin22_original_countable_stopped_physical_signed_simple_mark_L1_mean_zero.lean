-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_countable_stopped_physical_signed_simple_mark_L1_mean_zero
-- name    : AvramDividend.Classical.avram_mathfin22_original_countable_stopped_physical_signed_simple_mark_L1_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:00:44.737894+00:00
-- url     : https://prove2.me/theorems/14e8d8f5-ed23-411e-bba0-3f99abb5f9c5
-- title:
--   True original stopped signed NX simple-mark integral L1 and mean zero at bounded countably-valued clocks
-- statement:
--   An original-physical-process stopped Itô–Meyer jump-mark building block: for a bounded countably-valued right-continuous stopping time τ and a bounded finite-range negative mark function g on any Borel set separated from zero, the true signed compensated physical jump integral over (0,τ] is integrable and has expectation zero. Apply the newly ACCEPTED 33026332 original simple negative mark count-process bounded optional-stopping theorem, with no globally finite negative jump activity. Then identify the stopped count sum, path by path for each ω, with the actual NX signed integral minus its time-clock ν compensator using the independently ACCEPTED e4e5295a original physical fibre identity. The equality is exact at the physical random horizon (τ ω).untopA; no synthetic stochastic process or new premise about martingales is imposed. This supports localisation, predictable step-function mark coefficients and full stopped jump integrals in the Avram source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_actual_simple_negative_mark_countable_stop_mean_zero_unconditional_20261122
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_local_simple_compensated_fibre_identity
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_original_countable_stopped_physical_signed_simple_mark_L1_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (hSep : S ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (hν : X.ν S < ⊤)
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτbound : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let R : Ω → ℝ := fun ω =>
      (∫ p in Ioc 0 (τ ω).untopA ×ˢ S, g p.2 ∂(NX ω)) -
        (((τ ω).untopA : ℝ) * (∫ z in S, g z ∂X.ν))
    Integrable R P ∧ (∫ ω, R ω ∂P) = 0 := by sorry
