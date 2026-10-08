-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_of_gaussian
-- name    : AvramDividend.Classical.esscher_positive_root_of_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:10:17.843062+00:00
-- url     : https://prove2.me/theorems/1913f43f-2d52-485a-889c-d4ba935ed119
-- title:
--   Gaussian Lévy process has a positive Esscher root under canonical exponent continuity
-- statement:
--   A canonical Gaussian spectrally negative Lévy process has ψ(θ)>q beyond some finite θ for any q>0, by the already Proved Gaussian growth theorem. If its ψ is continuous on the nonnegative axis and ψ(0)=0, the already Proved intermediate-value root lemma yields a strictly positive φ solving ψ(φ)=q. This isolates the exact Gaussian Esscher root step of excursion-height factorisation.
-- source:
--   Proved psi_eventually_gt_of_gaussian and positive_continuous_root_from_growth, with exact source definition ψ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_positive_root_of_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ)
    (hcont : ContinuousOn X.ψ (Ici (0 : ℝ))) (hzero : X.ψ 0 = 0) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by sorry
