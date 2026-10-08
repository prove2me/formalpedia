-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_eventually_positive_quadratic_of_eventually_gt
-- name    : AvramDividend.Classical.psi_eventually_positive_quadratic_of_eventually_gt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T18:00:37.98397+00:00
-- url     : https://prove2.me/theorems/260593e3-4f9e-4e5a-aaa8-b88d5c9a7b5d
-- title:
--   Eventual positivity plus the universal Lévy quadratic bound gives a positive quadratic excess bound
-- statement:
--   For any canonical spectrally negative Lévy process, suppose ψ eventually lies above a fixed level q. The universal quadratic upper bound for ψ then yields, after increasing the cutoff to at least one and enlarging the coefficient by absolute values, a nonnegative constant C such that ψ(θ)-q≤C(1+θ²) on the same tail. This packages exactly the two process-level assumptions needed by the proved canonical strict-positivity theorem.
-- source:
--   Compose Proved psi_quadratic_upper with elementary real inequalities and the supplied eventual lower bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_quadratic_upper
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.psi_eventually_positive_quadratic_of_eventually_gt
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q β0 : ℝ)
    (hβ0 : 0 ≤ β0)
    (hgt : ∀ θ : ℝ, β0 ≤ θ → q < X.ψ θ) :
    ∃ β C : ℝ, 0 ≤ β ∧ 0 ≤ C ∧
      ∀ θ : ℝ, β ≤ θ →
        q < X.ψ θ ∧ X.ψ θ - q ≤ C * (1 + θ ^ 2) := by sorry
