-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_centered_jump_mean_zero
-- name    : AvramDividend.Classical.avram_p2_e_compensator_finite_nu_centered_jump_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:23:09.120014+00:00
-- url     : https://prove2.me/theorems/6e86d242-95e2-484a-af4c-60d8ee4874bc
-- title:
--   Original finite-band compensated marked jump increment is real-L¹ and centred
-- statement:
--   For the genuine original spectrally negative Lévy process, assume an independently sourced unconditional ν-rate on a Borel mark set B of finite ν-mass. The real intrinsic source jump count on (s,t], minus its deterministic rate (t-s)ν(B), is integrable and has expectation zero under the original probability measure. This is a genuine one-increment zero-mean bridge toward signed compensated jump martingales, without claiming the conditional martingale property or the canonical rectangle compensator.
-- source:
--   P2-E source real-L1 integrability 52b7e6d6 and real mean 14c106db (independent new helper proofs); original unconditional rate owned P2-D and remains Open. Pinned Mathlib integral_sub, integrable_const, probability measure normalization.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_finite_nu_centered_jump_mean_zero
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
        (Ioc s t ×ˢ B)).toReal - (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) P ∧
      (∫ ω, (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal - (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal ∂P) = 0 := by sorry
