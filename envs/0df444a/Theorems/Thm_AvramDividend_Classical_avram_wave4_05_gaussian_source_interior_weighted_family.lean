-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_interior_weighted_family
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_source_interior_weighted_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:38:59.842979+00:00
-- url     : https://prove2.me/theorems/559b9c25-32a2-41a2-b0ff-290c75ef4cf2
-- title:
--   Actual Gaussian q-scale generator interior weighted quadratic family
-- statement:
--   For the actual Standing spectrally negative Lévy process with a positive Gaussian coefficient and the original q-scale function, every sufficiently large admissible Laplace parameter has a verified compensated negative-jump interior slice bound quadratic in jump magnitude. The representative of W'' is the zero extension of the ordinary second derivative from strictly positive states; its weighted integrability is a source theorem, and the bound uses the actual source generatorIntegrand. This closes the Gaussian interior branch pending crossing-strip and large-jump assembly, without presuming a global generator identity.
-- source:
--   Source exact Gaussian q-scale C2, positive Esscher root, source eventual weighted curvature zero extension 9f9b8a9f, and canonically Proved source interior jump bound 0af79a05. Pinned Mathlib 0df444a, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43; Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_gaussian_source_interior_weighted_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      ∀ r : ℝ, 0 < r → r < 1 →
        let F : ℝ → ℝ :=
          (Ioi (0 : ℝ)).piecewise (deriv (deriv W)) (fun _ => 0)
        IntegrableOn
          (fun x : ℝ => Real.exp (-θ * x) *
            |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|)
          (Ioi r) volume ∧
        (∫ x in Ioi r, Real.exp (-θ * x) *
          |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) ≤
          (r ^ 2 / 2) *
            (∫ u : ℝ, Real.exp (-θ * u) * |F u|) := by sorry
