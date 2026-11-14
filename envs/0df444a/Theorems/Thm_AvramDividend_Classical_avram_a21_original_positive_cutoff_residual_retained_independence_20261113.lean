-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_positive_cutoff_residual_retained_independence_20261113
-- name    : AvramDividend.Classical.avram_a21_original_positive_cutoff_residual_retained_independence_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T09:23:59.932591+00:00
-- url     : https://prove2.me/theorems/58b1fdb4-de71-4c74-9b00-9b447a631cea
-- title:
--   True independence of original residual and disjoint retained compensated negative band at positive cutoff
-- statement:
--   The ORIGINAL Gaussian-plus-omitted-mark residual at positive cutoff is independent of the physically retained compensated negative jump band on the same Levy source probability space. This is the correct disjoint marked-band independence needed for source orthogonality, and differs from the disproved zero-cutoff residual independence.
-- source:
--   Levy Ito decomposition disjoint marked Poisson bands, Brownian component, characteristic function factorisation on the same probability space. True hard stochastic independence child of e83a2a28.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_positive_cutoff_residual_retained_independence_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      ProbabilityTheory.IndepFun
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) t ω)
        (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) t ω)
        P := by sorry
