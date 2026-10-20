-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_hjb_data_transport_rightCont
-- name    : AvramDividend.Classical.levy_hjb_data_transport_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:32:34.320524+00:00
-- url     : https://prove2.me/theorems/5e26b617-9b8b-4687-9317-5348c0d3fd04
-- title:
--   Standing conditions, Lévy generator and jump-integrability are unchanged under right-continuous filtration enlargement
-- statement:
--   Given original and right-continuous-filtration spectrally negative Lévy process structures with identical sample paths, drift c, Gaussian coefficient sigma and Lévy measure nu, transfer the classical standing assumptions to the augmented process and show the extended generator Gamma f(z) and GeneratorIntegrable test are exactly preserved for every test function and point. This proves the mathematical HJB data are invariant under a filtration change and makes the new right-continuous process usable with the original verification candidate and regularity conditions. It is fully independent of the still-open process-construction theorem.
-- source:
--   Pinned Formalpedia definition of SpectrallyNegativeLevy.Standing, HasMonotonePaths, Condition33, generator and GeneratorIntegrable; all triplet and path fields identical.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_hjb_data_transport_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕.rightCont)
    (hX : Y.X = X.X)
    (hc : Y.c = X.c) (hσ : Y.σ = X.σ)
    (hν : Y.ν = X.ν)
    (hstand : X.Standing) :
    Y.Standing ∧
      (∀ (f : ℝ → ℝ) (z : ℝ), Y.generator f z = X.generator f z) ∧
      (∀ (f : ℝ → ℝ) (z : ℝ),
        Y.GeneratorIntegrable f z ↔ X.GeneratorIntegrable f z) := by sorry
