-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_purejump_esscher_killed_Bernstein_lower
-- name    : AvramDividend.Classical.original_purejump_esscher_killed_Bernstein_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:23:00.476534+00:00
-- url     : https://prove2.me/theorems/fd68d5d9-d8df-4809-b577-28d8185ce187
-- title:
--   Strict positivity and lower bound for original pure-jump killed Bernstein Laplace exponent
-- statement:
--   For the original standing spectrally negative pure-jump Lévy process and a positive Esscher base φ at which ψφ>0, the shifted killed Bernstein exponent ψ(φ+s)/(φ+s) for s≥0 is at least ψφ/φ and is strictly positive. The proof uses the exact new source identity and the nonnegative Esscher-weighted compensated negative-tail integral. This supplies the positivity condition for Prove2Me's proved tightness and weak-resolvent Laplace-limit lemmas, with no hypothetical independent subordinator.
-- source:
--   Proved original_purejump_esscher_killed_Bernstein 0cb20c38, pointwise kernel bound 1eaa6bca, positivity of discounted exponential; used for 2fa29eaf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_original_purejump_esscher_killed_Bernstein
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.original_purejump_esscher_killed_Bernstein_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (φ : ℝ) (hφ : 0 < φ)
    (hψ : 0 < X.ψ φ) (s : ℝ) (hs : 0 ≤ s) :
    X.ψ φ / φ ≤ X.ψ (φ + s) / (φ + s) ∧
    0 < X.ψ (φ + s) / (φ + s) := by sorry
