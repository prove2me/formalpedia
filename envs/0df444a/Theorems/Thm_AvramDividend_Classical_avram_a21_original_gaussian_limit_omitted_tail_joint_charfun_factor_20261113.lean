-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_omitted_tail_joint_charfun_factor_20261113
-- name    : AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_joint_charfun_factor_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T10:24:24.125454+00:00
-- url     : https://prove2.me/theorems/2814ef45-cef2-4b55-9ad4-809f1b742622
-- title:
--   Original positive-time Gaussian limit and omitted negative-tail joint Fourier factorisation
-- statement:
--   The joint characteristic function of the same-source physical Gaussian limit and the physically OMITTED compensated near-zero negative mark tail factors into the two marginal characteristic functions, for every frequency pair, positive horizon, and cutoff. This is a precise original-space Gaussian versus Poisson independent component claim. It follows from Lévy-Khintchine / independent Lévy-Itô source components and is mathematically distinct from disproved independence between original zero-cutoff R0 and RETAINED negative band.
-- source:
--   Original same-source Lévy-Itô Gaussian plus compensated marked Poisson independent noise, joint characteristic function formula and disjoint mark bands; pinned Mathlib indepFun_iff_charFun_prod.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical WithLp
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_joint_charfun_factor_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω
      ∀ u : WithLp 2 (ℝ × ℝ),
        charFun (P.map (fun ω => toLp 2 (R t ω, J ω))) u =
          charFun (P.map (R t)) u.ofLp.1 *
          charFun (P.map J) u.ofLp.2 := by sorry
