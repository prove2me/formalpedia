-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18p2a_original_standing_jensen_psi
-- name    : AvramDividend.Classical.avram_ja18p2a_original_standing_jensen_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:37:30.608359+00:00
-- url     : https://prove2.me/theorems/4644a041-14e3-4499-ba9a-f4fa54df8e2e
-- title:
--   Jensen lower bound for original process Levy Laplace exponent
-- statement:
--   Under original Standing, the integrable original process X_1 has finite expectation and the Levy Laplace identity. Jensen's inequality implies theta times E X_1 is at most psi(theta) for 0<theta≤1, on the same probability space and filtration. This is the nontrivial probability child of bounded Laplace slope.
-- source:
--   J-A18 necessary Jensen child of Open ef4b3972.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18p2a_original_standing_jensen_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      θ * (∫ ω, X.X 1 ω ∂P) ≤
        laplaceExponent X.c X.σ X.ν θ := by sorry
