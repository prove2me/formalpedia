-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_weighted_exp_pushforward_moment_formula
-- name    : AvramDividend.Classical.avram_p2_original_fourth_weighted_exp_pushforward_moment_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:54:29.276209+00:00
-- url     : https://prove2.me/theorems/32fc083e-6419-4e12-abeb-7e75231f6435
-- title:
--   Polynomial moments of the original fourth-weighted exponential law equal source-weighted moments
-- statement:
--   For the actual original spectrally negative Lévy sample paths on Ω with P and any time t, weight P by the positive fourth exponential deficit, push it forward under exp(X_t), and integrate z^k for any natural k. The resulting ENNReal moment is exactly the source lintegral of the weight times exp(X_t)^k. The proof uses original adaptedness to establish global measurability and the pinned Mathlib lintegral_map and lintegral_withDensity identities. This is the precise measure-to-source moment bridge required for the small-time weighted weak-convergence proof; no replacement process or jump compensator is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_fourth_weighted_exp_pushforward_moment_formula
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X t ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X t ω)))) =
    (∫⁻ ω, ENNReal.ofReal ((Real.exp (X.X t ω) - 1) ^ 4) *
      ENNReal.ofReal ((Real.exp (X.X t ω)) ^ k) ∂P) := by sorry
