-- Prove2me | Theorems.Thm_BootstrapRecolorVerify_MetricGap_claim_6_3_exceptional
-- name    : BootstrapRecolorVerify.MetricGap.claim_6_3_exceptional
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:51.035194+00:00
-- url     : https://prove2.me/theorems/83014210-6f5a-4fac-8e27-905969b5aad5
-- title:
--   Claim 6.3 — Exceptional weighted length
-- statement:
--   There is an absolute spectral constant $C>0$ as in Appendix B.1 such that, for every sufficiently large recursion depth $r$, the accepted hierarchy law is a probability law and
--
--   $$\Pr\!\left[\frac1{N_r}\sum_{e\in E(G_r)}w_e\bigl(\operatorname{len}(e)-L^{1-\eta\operatorname{level}(e)}\bigr)\le1\right]\ge\frac12.$$
--
--   The law includes both independent cloud spectral resampling and conditional whole-lift-array sampling resampling. The subtracted baseline is exactly $2r$. Every exceptional edge retains its original weight, including edges of older levels newly marked at a later stage. This controls the additional LP objective caused by the exceptional lengths.
--
--   Differences from the source:
--   - encoding: a fixed spectral constant and probability after resampling → existence of that absolute constant, explicit conditional masses, and total mass one; reason: Appendix B.1 supplies the constant; normalization makes rejection-sampling existence explicit without assuming the exceptional-edge conclusion
--   - encoding: increase in total normalized weighted length over its baseline → sum of weighted increments edge by edge divided by Nᵣ; reason: each level has baseline 2 and each undirected edge is counted once with multiplicity, so the two expressions agree
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), Claim 6.3; Appendix B.1 and B.3 pp.30–33, p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=24; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Resampling

open scoped Classical

namespace BootstrapRecolorVerify.MetricGap

/-- Claim 6.3 p.24, under the accepted law, with Appendix B.1's fixed spectral
constant explicitly existentially chosen. Total mass one rules out failed
rejection sampling; no exceptional-edge conclusion is built into the law. -/
theorem claim_6_3_exceptional :
    ∃ C : ℝ, IsSpectralConstant C ∧ ∃ R : ℕ, 3 ≤ R ∧ ∀ r ≥ R,
      (∑ H : History r r, acceptedMass C H) = 1 ∧
      1 / 2 ≤ ∑ H : History r r,
        if excessWeightedLength H ≤ 1 then acceptedMass C H else 0 := by sorry

end BootstrapRecolorVerify.MetricGap
