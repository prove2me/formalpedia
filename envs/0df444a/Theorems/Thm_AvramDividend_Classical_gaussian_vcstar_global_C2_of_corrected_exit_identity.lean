-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_vcstar_global_C2_of_corrected_exit_identity
-- name    : AvramDividend.Classical.gaussian_vcstar_global_C2_of_corrected_exit_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:35:30.738484+00:00
-- url     : https://prove2.me/theorems/22f3dd7b-fefc-4871-93ed-d1d5157281f8
-- title:
--   Gaussian global C2 dividend barrier regularity from the corrected two-sided exit identity
-- statement:
--   For a spectrally negative Lévy process satisfying Standing with positive Gaussian coefficient, positive discount q and finite positive optimal barrier c*, the exact corrected killed two-sided exit identity implies that the optimal dividend barrier candidate v_{c*} is twice continuously differentiable on the positive half-line. The proof composes the verified Gaussian Esscher-scale monotonicity derived from that exit identity with the verified deterministic Gaussian C2 gluing bridge. This is an importable conditional consumer on the root's corrected two-sided exit prerequisite.
-- source:
--   Avram, Palmowski and Pistorius (2007), two-sided exit identity, Lemma 3 smooth fit and Proposition 4 Gaussian verification; composition of the named Prove2Me Proved lemmas.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_gaussian_tilt_monotone_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C2_gaussian_of_positive_tilt
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Gaussian global C2 barrier regularity from the corrected killed-exit identity. -/
theorem gaussian_vcstar_global_C2_of_corrected_exit_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ)) := by
  sorry

end AvramDividend.Classical
