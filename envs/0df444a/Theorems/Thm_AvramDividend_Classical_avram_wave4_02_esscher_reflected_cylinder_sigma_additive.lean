-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_cylinder_sigma_additive
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_reflected_cylinder_sigma_additive
-- status  : Open
-- author  : @WillR
-- created : 2026-10-31T16:05:48.443923+00:00
-- url     : https://prove2.me/theorems/2eaad5a6-76a9-4565-8537-8665d6194a86
-- title:
--   Genuine correlated Esscher-reflected cylinder content is sigma-subadditive
-- statement:
--   For the actual q-root positive Esscher law of a source SNLP reflected at the genuine running supremum, construct one normalised AddContent on measurable cylinders, exactly agreeing with every source finite-clock Esscher pushforward, and prove its sigma-subadditivity. This is the nontrivial missing Kolmogorov extension bridge for correlated finite-dimensional distributions. It must be proved from source projective consistency and compact-cylinder inner regularity; it may not be reduced to independent-coordinate piContent, to an arbitrary conditioned sigma-additive content, or to a hypothetical infinite Esscher path law. Once proved, Mathlib AddContent.measure yields an all-horizon product-coordinate path law. Further path cadlag/strong Markov and source marked-excursion PPP/compensation still remain needed for the Ito intensity and C1 excursion representation.
-- source:
--   Actual source projective family 03188b99, normalised cylinder content 23e12e91, compact inner regular marginals 9a4b63dc and cylinder compact regularity dd29e510. Generic non-pinned reference: Remy Degenne and Peter Pfaffelhuber KolmogorovExtension4, CompactSystem.lean, RegularContent.lean, KolmogorovExtension.lean (Apache 2.0); pinned Mathlib does not yet contain general correlated Kolmogorov extension theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_cylinder_content

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_reflected_cylinder_sigma_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ C : AddContent ℝ≥0∞
        (measurableCylinders (fun _ : ℝ≥0 => ℝ × ℝ)),
      C Set.univ = 1 ∧ C.IsSigmaSubadditive ∧
        ∀ (I : Finset ℝ≥0) (A : Set (I → ℝ × ℝ)),
          MeasurableSet A →
            C (cylinder I A) =
              (Measure.map
                (fun ω : Ω => fun i : I =>
                  (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
                (P.withDensity (fun ω => ENNReal.ofReal
                  (Real.exp (φ * X.X ((I.sup id) + 1) ω -
                    ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) A := by sorry
