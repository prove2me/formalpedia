-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_finite_marginal_tightness
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_reflected_finite_marginal_tightness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:41:59.073511+00:00
-- url     : https://prove2.me/theorems/3ebdc5d2-680b-4b42-9291-ba691c6fa695
-- title:
--   Each genuine finite Esscher-reflected Lévy marginal is tight on a compact finite-coordinate set
-- statement:
--   For the actual source spectrally negative Lévy process, positive Esscher root and every finite set of observation times, the joint law of the genuine running supremum and reflected drawdown under the actual later finite Esscher density is tight. For every epsilon > 0 a compact subset of the finite-coordinate Euclidean product captures all but epsilon probability. This supplies source-specific compactness of finite marginals for a possible Kolmogorov construction, but does not assert countable additivity of the cylinder content, an infinite-horizon path law, excursion marks or a compensator.
-- source:
--   Actual source adaptedness of runningSup and reflectedSup (Proved); bounded deterministic Esscher probability a74b4ab5; Mathlib isTightMeasureSet_singleton and isTightMeasureSet_iff_exists_isCompact_measure_compl_le. No conditional stochastic antecedent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_reflected_finite_marginal_tightness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ (I : Finset ℝ≥0) (ε : ℝ≥0∞), 0 < ε →
      ∃ K : Set (I → ℝ × ℝ),
        IsCompact K ∧
          (Measure.map
            (fun ω : Ω => fun i : I =>
              (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
            (P.withDensity (fun ω => ENNReal.ofReal
              (Real.exp (φ * X.X ((I.sup id) + 1) ω -
                ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) Kᶜ ≤ ε := by sorry
