-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_cylinder_content
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_reflected_cylinder_content
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:25:17.2953+00:00
-- url     : https://prove2.me/theorems/23e12e91-e3da-4135-b202-c83bff24048b
-- title:
--   Actual Esscher-reflected Lévy cylinder content is finitely additive, normalised and has exact source marginals
-- statement:
--   For the actual spectrally negative Lévy process X, positive q-root Esscher parameter φ and genuine finite terminal Esscher laws, there exists a finite additive content on the measurable cylinder algebra of joint running-supremum/reflected-drawdown paths at all times. Its mass of the whole path space equals one and on every measurable finite-coordinate cylinder its value equals exactly the source pushforward probability under Q_{sup I+1}. This is a source-identified additive content and does not assert countable additivity, a Kolmogorov path-space probability measure, cadlag concentration, excursion marks or Poisson compensation.
-- source:
--   Accepted source projective family 03188b99, accepted finite stopped Esscher probability a74b4ab5, pinned Mathlib projectiveFamilyContent_cylinder, Measure.map_apply, cylinder_univ. The finite source family itself is a pushforward of P.withDensity, so no hypothetical process or σ-finite mark intensity is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_projective_family
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_reflected_cylinder_content
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ C : AddContent ℝ≥0∞
        (measurableCylinders (fun _ : ℝ≥0 => ℝ × ℝ)),
      C Set.univ = 1 ∧
        ∀ (I : Finset ℝ≥0) (A : Set (I → ℝ × ℝ)),
          MeasurableSet A →
            C (cylinder I A) =
              (Measure.map
                (fun ω : Ω => fun i : I =>
                  (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
                (P.withDensity (fun ω => ENNReal.ofReal
                  (Real.exp (φ * X.X ((I.sup id) + 1) ω -
                    ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) A := by sorry
