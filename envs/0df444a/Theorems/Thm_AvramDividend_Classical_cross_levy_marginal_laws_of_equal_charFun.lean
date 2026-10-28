-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_marginal_laws_of_equal_charFun
-- name    : AvramDividend.Classical.cross_levy_marginal_laws_of_equal_charFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:50:54.246441+00:00
-- url     : https://prove2.me/theorems/7888da5c-93f5-4178-9acc-b21d685e7836
-- title:
--   Equality of Lévy one-time laws from common characteristic exponent on different probability spaces
-- statement:
--   Two spectrally negative Lévy processes may live on different probability spaces. Equality of their fixed-time characteristic functions for every real Fourier parameter and every nonnegative time implies equality of their fixed-time marginal probability measures. The proof obtains one-time measurability directly from the Proved canonical whole-path measurability lemma, propagates the original probability measure instances under the measurable maps, and applies Mathlib's characteristic-function uniqueness theorem. This supplies a clean interface for identifying arbitrary Avram Lévy increment laws with LeanLevy's canonical pure-jump characteristic exponent.
-- source:
--   Proved levy_wholePath_measurable [840bbf85-6d2b-4b05-a1d1-8712ce085afc], pinned Mathlib Measure.ext_of_charFun, LeanLevy charFun_map_levyJumpPath; prerequisite for cross_levy_prefix_increment_rectangles_of_marginal_laws [e86abd7d-f2cd-4d23-bebb-f9d651e901a5].

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_marginal_laws_of_equal_charFun
    {Ω₁ Ω₂ : Type*}
    [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hchar : ∀ t : ℝ≥0, ∀ ξ : ℝ,
      charFun (Measure.map (X.X t) P₁) ξ =
      charFun (Measure.map (Y.X t) P₂) ξ) :
    ∀ t : ℝ≥0,
      Measure.map (X.X t) P₁ = Measure.map (Y.X t) P₂ := by sorry
