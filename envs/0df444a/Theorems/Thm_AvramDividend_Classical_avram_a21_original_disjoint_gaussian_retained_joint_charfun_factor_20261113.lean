-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_disjoint_gaussian_retained_joint_charfun_factor_20261113
-- name    : AvramDividend.Classical.avram_a21_original_disjoint_gaussian_retained_joint_charfun_factor_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T09:30:35.276197+00:00
-- url     : https://prove2.me/theorems/87ac6a23-e22f-42b3-be2c-9d9fe001421d
-- title:
--   Original positive-cutoff disjoint Gaussian-residual and retained-jump joint characteristic function factorisation
-- statement:
--   Under the original Levy-process probability law, the joint characteristic function of the physical Gaussian-plus-omitted-mark residual and the compensated retained negative-mark band factorises into marginal characteristic functions for every frequency pair, positive horizon and positive cutoff. This is the precise source Poisson disjoint mark/Brownian independence input. Equivalent to physical independence, and distinct from the false zero-cutoff residual versus retained-band factorisation.
-- source:
--   Levy-Khintchine formula for original marked jump process and Gaussian source, plus disjoint marked Poisson measure independence; pinned Mathlib Probability.Independence.CharacteristicFunction indepFun_iff_charFun_prod.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical WithLp
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_disjoint_gaussian_retained_joint_charfun_factor_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (T : ℝ≥0), 0 < T →
      let R : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) T ω
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) T ω
      ∀ u : WithLp 2 (ℝ × ℝ),
        charFun (P.map (fun ω => toLp 2 (R ω, J ω))) u =
          charFun (P.map R) u.ofLp.1 *
          charFun (P.map J) u.ofLp.2 := by sorry
