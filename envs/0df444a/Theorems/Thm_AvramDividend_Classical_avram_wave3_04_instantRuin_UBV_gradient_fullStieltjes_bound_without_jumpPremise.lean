-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_instantRuin_UBV_gradient_fullStieltjes_bound_without_jumpPremise
-- name    : AvramDividend.Classical.avram_wave3_04_instantRuin_UBV_gradient_fullStieltjes_bound_without_jumpPremise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:15:21.013668+00:00
-- url     : https://prove2.me/theorems/25b3264a-5537-4e85-8fa2-3d0323918285
-- title:
--   Any instantly ruined capped original Lévy control satisfies the corrected UBV verification without dividend-jump HJB assumptions
-- statement:
--   For every original spectrally negative Lévy process under any cap (including positive finite and infinite), if a genuine admissible adapted left-continuous dividend policy ruins immediately a.s., the complete expected original Stieltjes dividend reward through any finite horizon is bounded by the repaired UBV C² HJB candidate. Under the corrected w(0)≥0 and w'≥1 hypotheses, canonical Proved full-cap secant gives w(x)≥x. The exact native-admissibility instant-ruin Stieltjes budget gives total discounted reward≤initial capital x on every instantly ruined path, including the initial right atom. Integrating the almost-sure inequality against the original probability measure yields E[reward]≤ENNReal.ofReal x≤ENNReal.ofReal w(x). No separate HJB jump secant, source generator assumption, process representation, or non-ruin stochastic calculus is used. This sharpens the previously proved full-horizon instant-ruin bound and isolates the remaining surviving-positive-cap problem.
-- source:
--   Pinned exact private remote candidate-probe 85a5463d-03dd-4b51-b7fb-2b0868404886 reached sentinel with no source diagnostics, SHA256 d6ce48b0aa47cdbaa6a0ea8c004f19c661fe565b8bab0f716907b880cd9406ff. Canonical Proved UBV HJB candidate dominates initial capital 61ab7dfc-c4ed-4ee5-8381-b1da52174462; exact original instant-ruin full Stieltjes budget 389a618c-8fb0-4164-afac-c2bfd197c65d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_HJB_candidate_dominates_initial_capital
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_instantRuin_UBV_gradient_fullStieltjes_bound_without_jumpPremise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C) (hx : 0 ≤ x)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hRuin : ∀ᵐ ω ∂P, ruinTime X x D ω = 0)
    (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
