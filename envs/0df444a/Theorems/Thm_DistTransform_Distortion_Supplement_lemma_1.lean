-- Prove2me | Theorems.Thm_DistTransform_Distortion_Supplement_lemma_1
-- name    : DistTransform.Distortion.Supplement.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T13:11:18.444704+00:00
-- url     : https://prove2.me/theorems/3603ab7c-1918-4a2f-aaae-b1e9320a5782
-- title:
--   Lemma 1 — convexity on the full bounded quantile cone
-- statement:
--   Fix any atomless probability space, and let ρ be a law-invariant convex risk measure on its full L∞ space of losses. For a bounded law F, let ρ̂(F) be the value of ρ on any representative of F. For arbitrary bounded laws F,G and every λ∈[0,1],
--
--   $$
--   \widehat\rho\bigl((\lambda\otimes F)\oplus((1-\lambda)\otimes G)\bigr)
--   \le\lambda\widehat\rho(F)+(1-\lambda)\widehat\rho(G).
--   $$
--
--   Here a⊗F is the law of aX for X∼F and F⊕G is the common-uniform, comonotonic sum. This transfers convexity of a risk measure to the distributional quantile cone and supplies the supporting result used by Theorem 3. Both λ=0 and λ=1 are included, and there is no normalization, continuity or Fatou assumption.
--
--   Differences from the source:
--   - encoding: laws on the source atomless probability space → all ProbabilityMeasure ℝ with Minf and an arbitrary atomless probability space for risks; reason: every bounded law is realizable there; no finite or discrete restriction is introduced
--   - encoding: L∞ random variables and Definition 4 → published measurable essentially bounded functions with almost-sure order and the same risk axioms; reason: monotonicity identifies almost-surely equal representatives; cash invariance in subtraction form is the same loss convention
--   - encoding: ρ̂ of a law-invariant risk → a subtype carrying law invariance and rhoHat_eq for every representative; reason: the construction is independent of representatives and is never defined for a non-law-invariant input
--   - encoding: nonnegative multiplication and comonotonic addition → affine pushforwards including zero and definite description of the law by its interior quantiles; reason: these are the same cone operations and retain both endpoints of the convex mixture
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), p. 16, Lemma 1 and its proof; p. 15, standing domain and Definition 4

import Mathlib
import Definitions.Def_DistTransform_Distortion_Supplement_RiskModel

namespace DistTransform.Distortion.Supplement

open MeasureTheory

/-- Lemma 1, p. 16, on the full bounded quantile cone and at both mixture endpoints. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (ρ : LawInvariantRisk P)
    (hρ : TailRiskTheory.Generator.IsConvexRiskMeasure P ρ.val) :
    ∀ F ∈ Minf, ∀ G ∈ Minf, ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      rhoHat P ρ (comonoSum (affineLaw lam 0 F) (affineLaw (1 - lam) 0 G)) ≤
        lam * rhoHat P ρ F + (1 - lam) * rhoHat P ρ G := by sorry

end DistTransform.Distortion.Supplement
