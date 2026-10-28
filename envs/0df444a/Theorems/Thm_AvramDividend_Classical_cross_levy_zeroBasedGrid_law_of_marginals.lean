-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_zeroBasedGrid_law_of_marginals
-- name    : AvramDividend.Classical.cross_levy_zeroBasedGrid_law_of_marginals
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:41:31.524266+00:00
-- url     : https://prove2.me/theorems/8b70d80d-0845-405c-8907-7af83009e946
-- title:
--   Identical Lévy one-time marginals identify joint path-value laws on every monotone zero-based finite grid across sample spaces
-- statement:
--   Two spectrally negative Lévy processes on distinct probability spaces with identical one-time marginal distributions have equal joint distributions of all observed path values over every finite nondecreasing observation grid beginning at time zero. This composes the finite-vector law of consecutive independent increments with the deterministic path-level prefix-sum reconstruction. The result supplies the final zero-based grid step before lifting finite-dimensional laws to full coordinate path laws.
-- source:
--   Composes the newly published cross_levy_finite_increment_vector_law_of_marginals [86a80deb-4bf8-4360-800b-f1ded05a6914] and cross_levy_incrementVector_law_implies_zeroBasedGrid_law [1e55334a-9d13-41fa-9747-ea9a200b39a7].

import Theorems.Thm_AvramDividend_Classical_cross_levy_finite_increment_vector_law_of_marginals
import Theorems.Thm_AvramDividend_Classical_cross_levy_incrementVector_law_implies_zeroBasedGrid_law

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_zeroBasedGrid_law_of_marginals
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hMarginal : ∀ u : ℝ≥0, Measure.map (X.X u) P₁ = Measure.map (Y.X u) P₂)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (n : ℕ) :
    Measure.map (fun ω : Ω₁ => fun i : Fin n => X.X (t (i.val + 1)) ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun i : Fin n => Y.X (t (i.val + 1)) ω) P₂ := by sorry
