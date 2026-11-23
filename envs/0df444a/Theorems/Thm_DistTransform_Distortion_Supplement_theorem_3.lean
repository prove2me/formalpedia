-- Prove2me | Theorems.Thm_DistTransform_Distortion_Supplement_theorem_3
-- name    : DistTransform.Distortion.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T13:13:14.235596+00:00
-- url     : https://prove2.me/theorems/8ce3d93d-e4c5-4d8f-bc89-4a50287f64a6
-- title:
--   Theorem 3 — increasing convex order and preservation of convex and coherent risks
-- statement:
--   Fix any atomless probability space and the full L∞ domain of real losses. Let T:M∞→M∞ be monotone for stochastic order and scale-location invariant: it commutes with the law of aX+b for every a≥0 and b∈ℝ. Write Rcx for monetary convex risk measures and Rch for monetary convex positively homogeneous risk measures. For a law-invariant input ρ, write ρ_T(X)=ρ̂(T(F_X)). Then the following four conditions are equivalent:
--
--   $$
--   \begin{aligned}
--   \text{(i)}\;&T\text{ is }\preceq_{\mathrm{icx}}\text{-monotone and }\preceq_{\mathrm{icx}}\text{-subadditive};\\
--   \text{(ii)}\;&\rho_T\in\mathcal R_{\mathrm{cx}}\quad\text{for every law-invariant }\rho\in\mathcal R_{\mathrm{cx}};\\
--   \text{(iii)}\;&\rho_T\in\mathcal R_{\mathrm{ch}}\quad\text{for every law-invariant }\rho\in\mathcal R_{\mathrm{ch}};\\
--   \text{(iv)}\;&(\mathrm{ES}_p)_T\in\mathcal R_{\mathrm{ch}}\quad\text{for every }0<p<1.
--   \end{aligned}
--   $$
--
--   Increasing-convex subadditivity means T(F⊕G)≼icxT(F)⊕T(G) for every bounded F,G. Expected Shortfall is the upper quantile average ES_p(F)=(1−p)⁻¹∫_p^1F⁻¹(t)dt. The input restriction to law invariance is inherited from the definition of ρ̂ at the top of p. 16; the classes Rcx and Rch themselves are precisely Definition 4. The theorem tests arbitrary monotone scale-location invariant transforms, with no additivity or shape-commutation premise, and characterizes preservation of the entire risk classes.
--
--   Differences from the source:
--   - encoding: laws on the source atomless probability space → all ProbabilityMeasure ℝ with Minf and an arbitrary atomless probability space for risks; reason: every bounded law is realizable there; no finite or discrete restriction is introduced
--   - encoding: L∞ random variables and Definition 4 → published measurable essentially bounded functions with almost-sure order and the same risk axioms; reason: monotonicity identifies almost-surely equal representatives; cash invariance in subtraction form is the same loss convention
--   - reading: Theorem 3(ii),(iii) quantify over Rcx and Rch → quantification over their law-invariant members as inputs to ρ_T; reason: p. 16 defines ρ̂ and ρ_T only for law-invariant input risks, and p. 17 explicitly uses law invariance; Rcx and Rch themselves are unchanged
--   - encoding: T:M∞→M∞ and scale-location invariance → MapsTo T Minf Minf and commutation for every a≥0,b∈ℝ, retaining domain closure; reason: the ambient total function changes no bounded-law instance and the zero scale is included
--   - encoding: all four statements are equivalent → List.TFAE with exactly the four source conditions; reason: every direction is asserted, with both icx properties in (i) and every interior ES level in (iv)
--   - encoding: ∫_p^1 F⁻¹(t)dt for ES_p → Lebesgue integral over (p,1); reason: the removed endpoints are null; 0<p<1 guards the denominator and the integral uses only finite interior quantiles
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), pp. 16–17, Theorem 3 and proof; pp. 13–16, Definitions 3–4 and standing risk setting

import Mathlib
import Definitions.Def_DistTransform_Distortion_Supplement_Orders
import Definitions.Def_DistTransform_Distortion_Supplement_RiskModel

namespace DistTransform.Distortion.Supplement

open MeasureTheory

/-- Theorem 3, pp. 16–17. All four conditions are equivalent on every
atomless probability space; Rcx and Rch are the unmodified risk classes.
Only inputs to ρ_T have the source's standing law-invariance restriction. -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ)
    (hT : Set.MapsTo T Minf Minf) (hmono : IsMonotoneT Minf T)
    (hscale : IsScaleLocationInvariant T) :
    List.TFAE [
      IsIcxMonotone T ∧ IsIcxSubadditive T,
      ∀ ρ : LawInvariantRisk P,
        TailRiskTheory.Generator.IsConvexRiskMeasure P ρ.val →
          TailRiskTheory.Generator.IsConvexRiskMeasure P (generated P ρ T),
      ∀ ρ : LawInvariantRisk P,
        TailRiskTheory.Generator.IsCoherent P ρ.val →
          TailRiskTheory.Generator.IsCoherent P (generated P ρ T),
      ∀ p ∈ Set.Ioo (0 : ℝ) 1,
        TailRiskTheory.Generator.IsCoherent P (generatedES P T p)] := by sorry

end DistTransform.Distortion.Supplement
