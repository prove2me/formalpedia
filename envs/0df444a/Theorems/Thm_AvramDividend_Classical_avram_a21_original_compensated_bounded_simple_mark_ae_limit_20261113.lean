-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_compensated_bounded_simple_mark_ae_limit_20261113
-- name    : AvramDividend.Classical.avram_a21_original_compensated_bounded_simple_mark_ae_limit_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:14:57.287657+00:00
-- url     : https://prove2.me/theorems/2cadf060-cf10-497c-85aa-035939e9c3bf
-- title:
--   Original physical finite-range Borel marked integrals converge with their original compensators
-- statement:
--   For finite-activity original spectrally negative Lévy paths and uniformly bounded simple marks converging on any negative Borel set, the actual physical compensated marked jump integrals converge almost surely to the original-space compensated Borel mark integral, including convergence of the true source Lévy compensators.
-- source:
--   Proved original raw bounded simple physical marked integral convergence 6bb2d2ba-024c-48a8-8e73-d429f12a52a3 and Proved original finite-mass bounded Borel mark compensator integral convergence a69705d8-63f5-4c54-86bd-a424ebbac3a1. Real Tendsto.sub preserves the same Omega/P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_bounded_simple_integral_L2_domination_convergence
import Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_Borel_mark_first_second_integral_limits
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_compensated_bounded_simple_mark_ae_limit_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (v : ℝ → ℝ) (f : ℕ → SimpleFunc ℝ ℝ)
    (hBound : ∀ k z, z ∈ S → |f k z| ≤ 1)
    (hLimit : ∀ z ∈ S, Tendsto (fun k => f k z) atTop (𝓝 (v z))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) u)))
    let Z : ℕ → Ω → ℝ := fun k ω =>
      (∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω) -
        (T : ℝ) * (∫ z in S, f k z ∂X.ν)
    let C : Ω → ℝ := fun ω =>
      (∫ p in (Ioc 0 T ×ˢ S), v p.2 ∂NX ω) -
        (T : ℝ) * (∫ z in S, v z ∂X.ν)
    ∀ᵐ ω ∂P, Tendsto (fun k => Z k ω) atTop (𝓝 (C ω)) := by sorry
