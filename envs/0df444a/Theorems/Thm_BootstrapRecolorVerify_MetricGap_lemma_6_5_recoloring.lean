-- Prove2me | Theorems.Thm_BootstrapRecolorVerify_MetricGap_lemma_6_5_recoloring
-- name    : BootstrapRecolorVerify.MetricGap.lemma_6_5_recoloring
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:41.266471+00:00
-- url     : https://prove2.me/theorems/bb2c3615-66da-4839-80a3-c780d55f00a1
-- title:
--   Lemma 6.5 — Recoloring, including stage two
-- statement:
--   Fix an absolute spectral constant $C$ with the source's uniform success property. For all sufficiently large $r$, let $2\le s\le r$ and let $\varphi_s:V(G_s)\to V(G_s)$ be monochromatic at level $s$ in an accepted hierarchy. Collapse those clouds, choose independent uniform representatives in the level-$(s-1)$ clouds, and project their original colors onto $G_{s-1}$. The resulting random map $\varphi_{s-1}$ is monochromatic at level $s-1$ for every outcome, and
--
--   $$\mathbb E\overline{\operatorname{cost}}_{s-1}(\varphi_{s-1})\le\frac{D}{\lambda_2^*}\overline{\operatorname{cost}}_s(\varphi_s)+4(s-3)^+\theta b.$$
--
--   At $s=2$, the stronger bound holds:
--
--   $$\mathbb E\overline{\operatorname{cost}}_1(\varphi_1)\le\overline{\operatorname{cost}}_2(\varphi_2).$$
--
--   Here $x^+=\max(x,0)$, $\lambda_2^*=1-C/L$, and $b=M_1/(2L)$. Both expectations use the specified product-uniform representative law. This is the full quantitative recoloring statement, including its boundary-stage conclusion.
--
--   Differences from the source:
--   - generalization: one fixed absolute spectral constant C₁ supplied by Appendix B.1 → any fixed C satisfying the same uniform spectral-success property; reason: all estimates use only this property and a sufficiently-large threshold allowed to depend on C; the source constant is included
--   - generalization: the realization fixed after Claim 6.3 also has exceptional weighted-length increase at most 1 → every history satisfying the spectral and sampling acceptance events, without the exceptional-length bound; reason: Appendix B.4 and the proofs of Lemmas 6.5 and 6.7 do not use the length bound; every source realization satisfies these acceptance events, so the full source claim is included
--   - encoding: source stage s≥2 and the random map constructed by representatives → s=i+2 with i natural and the explicit map recolorDown; reason: all source stages occur, and choosing coordinate zero when collapsing a monochromatic cloud does not change its common color
--   - encoding: positive sufficiently large recursion depth and standing resampling conditions → an explicit 0<r proof argument and Accepted C H; reason: the positivity argument only defines a cloud coordinate; it excludes no r in the sufficiently-large source regime
--   - encoding: positive-part error (s−3)⁺ → max((i:ℝ)−1,0); reason: substitution s=i+2 preserves the exact error at every stage, including s=2 and s=3
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), Lemma 6.5, (22), proof pp.25–27, p.25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=25; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Resampling

open scoped Classical

namespace BootstrapRecolorVerify.MetricGap

/-- Lemma 6.5 p.25, (22), including the stage-two improvement. The source's
stage is i+2, avoiding dependent predecessor casts. Randomness is the actual
independent uniform representative array of pp.25--26. -/
theorem lemma_6_5_recoloring (C : ℝ) (hC : IsSpectralConstant C) :
    ∃ R : ℕ, 3 ≤ R ∧ ∀ r ≥ R, ∀ hr : 0 < r, ∀ i, i + 2 ≤ r →
      ∀ H : History r (i + 2), Accepted C H →
        ∀ f : Vertex r (i + 2) → Vertex r (i + 2), Monochromatic f →
          (∀ z : Representatives r i, Monochromatic (recolorDown hr f z)) ∧
          average (fun z : Representatives r i =>
            proxyCost H.1 (recolorDown hr f z)) ≤
            distortion r / spectralGap r C * proxyCost H f +
              4 * max ((i : ℝ) - 1) 0 * theta r * baseBound r ∧
          (i = 0 → average (fun z : Representatives r i =>
            proxyCost H.1 (recolorDown hr f z)) ≤ proxyCost H f) := by sorry

end BootstrapRecolorVerify.MetricGap
