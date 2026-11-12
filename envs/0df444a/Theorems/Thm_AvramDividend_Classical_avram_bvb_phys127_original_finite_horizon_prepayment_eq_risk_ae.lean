-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys127_original_finite_horizon_prepayment_eq_risk_ae
-- name    : AvramDividend.Classical.avram_bvb_phys127_original_finite_horizon_prepayment_eq_risk_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:53:38.057759+00:00
-- url     : https://prove2.me/theorems/afdf8c99-ab23-4a78-87d6-b9a7e323c004
-- title:
--   Original finite-horizon source-free prepayment reserve equals risk almost everywhere
-- statement:
--   On the true original finite-horizon zero-source-jump event used by phys95, the genuine prepayment physical reserve U(t) agrees with the actual riskProcess at Lebesgue-almost every positive t≤S. The proof combines original admissibility's a.e. dividend continuity with the proved finite-horizon source left-limit identity phys126 and preserves the original source, dividend and ruin conventions.
-- source:
--   Proved phys116 original dividend a.e. continuity and phys126 finite-horizon source prepayment leftLim identity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys127_original_finite_horizon_prepayment_eq_risk_ae {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (μ : Measure ℝ≥0) [NullSingletonClass μ] (ω : Ω) (S : ℝ≥0) (hsource : ∀ s : ℝ≥0, s ≤ S → X.X s ω = (s : ℝ) * X.drift) : ∀ᵐ t ∂μ, 0 < (t : ℝ≥0) → t ≤ S → Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = riskProcess X x D t ω := by sorry
