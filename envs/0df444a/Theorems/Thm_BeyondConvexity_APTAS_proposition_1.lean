-- Prove2me | Theorems.Thm_BeyondConvexity_APTAS_proposition_1
-- name    : BeyondConvexity.APTAS.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:16:01.7982+00:00
-- url     : https://prove2.me/theorems/45fa0e2f-5ff0-41d1-8aa2-3e6d36c3e8aa
-- title:
--   Proposition 1 — uniform bulk inequality
-- statement:
--   Let $\mathcal P$ be a class of valid rational polygonal regions with a uniform rasterization resolution $\Pi$. Set $\lambda=\frac16\min\{\Pi(1/2),1/2\}$. Then $\lambda>0$ and every $P\in\mathcal P$ satisfies
--
--   $$\operatorname{Area}(P)\ge\lambda D(P)^2.$$
--
--   Here $D$ is Euclidean diameter, and holes contribute no area. This relates area and squared diameter with the paper’s explicit constant, independently of the object and its boundary complexity.
--
--   Differences from the source:
--   - encoding: uniformly rasterizable class of polygonal objects with resolution Π → an explicit RasterWitness and an explicit validity guard on each region; reason: the constant depends on the chosen witness; validity spells out the standing Section 2 object convention
--   - encoding: real constant λ and planar area → rational bulkConstant coerced to the reals and Lebesgue volume.toReal; reason: the resolution is rational-valued and valid compact polygonal regions have finite area
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Proposition 1, printed p.6 / PDF p.7, equation (4); proof Appendix A.2, printed p.18 / PDF p.19.

import Definitions.Def_BeyondConvexity_APTAS_RasterWitness

namespace BeyondConvexity.APTAS

/-- Silva, Dell'Arriva, Miyazawa, STOC 2027 submission #890 (October 2026),
Proposition 1, printed p.6 / PDF p.7, equation (4); proof A.2, printed p.18 / PDF p.19.
The resolution witness is exposed because the explicit constant depends on its value at 1/2. -/
theorem proposition_1 (P : Set Polygon) (resolution : ℚ → ℚ)
    (hRaster : RasterWitness P resolution) :
    0 < bulkConstant resolution ∧
      ∀ p ∈ P, p.Valid →
        (bulkConstant resolution : ℝ) * p.diameter ^ 2 ≤ area p.region := by sorry

end BeyondConvexity.APTAS
