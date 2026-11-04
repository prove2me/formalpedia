-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
-- name    : AvramDividend.Classical.avram_p2_e_compensator_finite_nu_count_real_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:15:47.153622+00:00
-- url     : https://prove2.me/theorems/52b7e6d6-9c85-42c5-a164-516c6ac156a2
-- title:
--   Finite-rate original intrinsic marked jump counts are real-L¹ integrable
-- statement:
--   For the original spectrally negative Lévy process X and any Borel mark set B with finite original Lévy measure ν(B), a separately proved original unconditional rate E[N_X((s,t]×B)]=(t-s)ν(B) implies integrability of the real conversion of the literal intrinsic marked count. This supplies the L¹ domain needed for signed compensated jump martingales without assuming a Poisson replacement or a compensator theorem.
-- source:
--   P2-E Proved genuine source count measurability 8146a449; pinned Mathlib integrable_toReal_of_lintegral_ne_top and ENNReal.mul_lt_top; external original ν-rate P2-D 859bf7be.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_finite_nu_count_real_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    Integrable (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal) P := by sorry
