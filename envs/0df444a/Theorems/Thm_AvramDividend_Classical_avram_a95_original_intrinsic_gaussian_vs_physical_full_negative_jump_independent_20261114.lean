-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a95_original_intrinsic_gaussian_vs_physical_full_negative_jump_independent_20261114
-- name    : AvramDividend.Classical.avram_a95_original_intrinsic_gaussian_vs_physical_full_negative_jump_independent_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T18:49:08.188236+00:00
-- url     : https://prove2.me/theorems/4679488b-c179-4da9-b4ba-c0e25413440e
-- title:
--   Original intrinsic Gaussian residual independent of complete finite-activity physical negative-jump total
-- statement:
--   On the original filtered Lévy probability space with finite negative activity and positive Gaussian variance, a measurable version H of the intrinsic continuous Gaussian residual at time t is independent of any measurable version J of the complete physical negative-jump sum at the same time. Both are on the same original sample space; no auxiliary Brownian noise, full-path raw-F0 event, or zero-mark simplification is assumed. This source independence implies all exponential factorisations for arbitrary real tilts by measurable transformation.
-- source:
--   Finite-activity original Lévy–Itô Gaussian/marked-jump component independence; can use original bounded-disjoint-mark characteristic functions, original future-path law, Mathlib IndepFun. This is the genuine analytic independence obligation needed by A71.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a95_original_intrinsic_gaussian_vs_physical_full_negative_jump_independent_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ) (hNu : X.ν ≠ 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (t : ℝ≥0) (ht : 0 < t)
    (H J : Ω → ℝ)
    (hHMeas : Measurable H) (hJMeas : Measurable J)
    (hHEq : H =ᵐ[P] R t)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    : IndepFun H J P := by sorry
