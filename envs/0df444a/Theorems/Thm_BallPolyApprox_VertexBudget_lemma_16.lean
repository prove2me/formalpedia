-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_lemma_16
-- name    : BallPolyApprox.VertexBudget.lemma_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:56:19.572658+00:00
-- url     : https://prove2.me/theorems/285ede99-2a25-4ade-a44a-d127040cf7d1
-- title:
--   Lemma 16 — under the boundary law $\nu$, $|Y|^2=H+(1-H)Q_d$ with $H$ independent of $Q_d$
-- statement:
--   Under the standing assumptions of §5.3.1 ($d$ sufficiently large, $M\ge2d$): under the boundary law $\nu$ of (38),
--   $$|Y|^2=H+(1-H)Q_d,$$
--   where $H$, the squared distance of the supporting hyperplane from the origin, has density proportional to $(1-t)^{d(d-1)/2-1}G_d(t)^{M-d}$ on $0<t<1$, and $Q_d$ is independent of $H$ and follows the squared-simplex-volume angular law (21). In particular $0\le Q_d\le1$.
--
--   Formally: for every measurable $g\ge0$ on $\mathbb R^2$, $\mathbb E_\nu\,g(H,|Y|^2)=\int\!\!\int g\big(t,t+(1-t)q\big)\,dQ_d(q)\,dH(t)$, and the law of $Q_d$ gives $[0,1]$ full mass.
--
--   Differences from the source:
--   - encoding: §5.3.1 standing assumption: d sufficiently large, M ≥ 2d → ∃ d0, ∀ d ≥ d0, ∀ M ≥ 2d; reason: the subsection's standing assumption written as hypotheses; it changes no instance the source covers
--   - encoding: |Y|² = H + (1 − H)Q_d with Q_d independent of H → for every measurable g ≥ 0, E_ν g(H, |Y|²) = ∫∫ g(t, t + (1 − t)q) dQ_d(q) dH(t); reason: the joint law of (H, |Y|²) is that of (H, H + (1 − H)Q_d) with independent factors; since H < 1 a.s. this is equivalent to (H, (|Y|² − H)/(1 − H)) having the product law
--   - encoding: ν as a sum over facets (38) and H as the facet's hyperplane distance → gauge encoding of ν and H = 1/|a|² for the supporting hyperplane ⟨a, z⟩ = 1 at Y (supremum over such hyperplanes); reason: equal to (38) because P contains o in its interior a.s. and radial projection of a uniform point of conv{o, F} is uniform on F; the hyperplane is unique for ν-a.e. Y
--   - encoding: In particular, 0 ≤ Q_d ≤ 1 → the law of Q_d gives the complement of [0, 1] measure 0; reason: an almost-sure bound on a random variable given by its law
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), Lemma 16, p. 17 (PDF 19)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer
import Definitions.Def_BallPolyApprox_VertexBudget_AngularLaw
import Definitions.Def_BallPolyApprox_VertexBudget_RandomPolytope

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

/-- Lemma 16 (p. 17, PDF 19), under the standing assumptions of §5.3.1 (`d` sufficiently large,
`M ≥ 2d`): under the boundary law `ν` of (38), `|Y|² = H + (1 − H) Q_d` in law, where `H` (the
squared distance of the supporting hyperplane from the origin) has density proportional to
`(1 − t)^{d(d−1)/2−1} G_d(t)^{M−d}` on `(0, 1)` and `Q_d` is independent of `H` with the
squared-simplex-volume angular law (21): for every measurable test function `g ≥ 0`,
`E_ν g(H, |Y|²) = ∫∫ g(t, t + (1 − t) q) dQ_d(q) dH(t)`. In particular `0 ≤ Q_d ≤ 1`. -/
theorem lemma_16 :
    ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d → ∀ M : ℕ, 2 * d ≤ M →
      (∀ g : ℝ × ℝ → ENNReal, Measurable g →
        nuExp d M (fun P y => g (supportSqDist P y, ‖y‖ ^ 2)) =
          ∫⁻ t, ∫⁻ q, g (t, t + (1 - t) * q) ∂QLaw d ∂lawH d M) ∧
      QLaw d (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by sorry

end BallPolyApprox.VertexBudget
