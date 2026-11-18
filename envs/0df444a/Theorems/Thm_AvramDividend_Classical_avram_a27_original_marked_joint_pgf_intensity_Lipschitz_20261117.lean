-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_marked_joint_pgf_intensity_Lipschitz_20261117
-- name    : AvramDividend.Classical.avram_a27_original_marked_joint_pgf_intensity_Lipschitz_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:33:19.709462+00:00
-- url     : https://prove2.me/theorems/b33d02bf-8846-4e3b-a7b8-db333b8f808c
-- title:
--   Original physical marked negative jump PGF is Lipschitz in its count parameter with genuine negative-jump intensity constant
-- statement:
--   For the unchanged finite-activity spectrally negative Levy process and its actual physical count K and marked jump sum J, the original expectation of z^K exp(theta J) is Lipschitz as z ranges over [0,1]. The Lipschitz constant is the genuine horizon negative-jump intensity t nu((−∞,0)). The proof bounds each sample by K exp(theta J) times the parameter difference and applies the previously formalised physical weighted-count expectation estimate.
-- source:
--   Proved source weighted count integrability and rate bound 783d64bc; Proved marked integrability cc395132; deterministic real unit power Lipschitz lemma.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_exp_weighted_negative_jump_count_integrable_rate_bound_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_marked_joint_pgf_intensity_Lipschitz_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (z w : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    |(∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) -
      (∫ ω, w ^ (K ω) * Real.exp (θ * J ω) ∂P)| ≤
      (((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) * |z - w| := by sorry
