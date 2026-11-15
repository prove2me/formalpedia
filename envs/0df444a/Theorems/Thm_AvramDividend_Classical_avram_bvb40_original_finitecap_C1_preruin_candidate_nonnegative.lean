-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb40_original_finitecap_C1_preruin_candidate_nonnegative
-- name    : AvramDividend.Classical.avram_bvb40_original_finitecap_C1_preruin_candidate_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:24:35.985743+00:00
-- url     : https://prove2.me/theorems/5407435b-478d-4819-a271-6497a90fbc3b
-- title:
--   Original finitecap C1 HJB slope and admissibility imply nonnegative actual pre-ruin candidate payoff
-- statement:
--   For the original spectrally negative Lévy process X and actual admissible capped dividend D, show the actual prepayment reserve U_t is in [0,C] strictly before ruin, then combine the original C1 derivative at least one and nonnegative w(0) to conclude w(U_t)≥0. This removes the separately assumed original pre-ruin candidate nonnegativity from BV-B and supports the full stopped dividend cash source. Theorem requires only C1 interior regularity, strictly weaker than the existing Proved C2 version. Source exactly Proved capped_riskProcess_range_before_ruin_including_zero 15c076b4 and original finite-cap global secant 849da3fc.
-- source:
--   Proved 15c076b4 and 849da3fc, no new stochastic compensation or imported affine postpayment process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb40_original_finitecap_C1_preruin_candidate_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by sorry
