-- Prove2me | Theorems.Thm_CompOT_Sinkhorn_remark_4_12_distance
-- name    : CompOT.Sinkhorn.remark_4_12_distance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:12.115464+00:00
-- url     : https://prove2.me/theorems/c6e6f335-b3ad-44ec-8247-b936555db108
-- title:
--   Remark 4.12, p. 439 — d_H is a distance on the projective cone: triangle inequality, d_H(u, u′) = 0 iff u = r u′
-- statement:
--   Let $n \ge 1$ and let $u, u', u'' \in \mathbb{R}^n$ have positive entries. Hilbert's projective metric $d_{\mathcal H}$ is a distance on the rays of the positive cone:
--
--   1. $d_{\mathcal H}(u,u') \ge 0$;
--   2. $d_{\mathcal H}(u,u') = d_{\mathcal H}(u',u)$;
--   3. $d_{\mathcal H}(u,u'') \le d_{\mathcal H}(u,u') + d_{\mathcal H}(u',u'')$;
--   4. $d_{\mathcal H}(u,u') = 0$ if and only if $u = r u'$ for some $r > 0$.
--
--   That is, $d_{\mathcal H}$ is a metric on the projective cone $\mathbb{R}^n_{+,*}/\!\sim$, where $u \sim u'$ means that the two vectors agree up to a positive factor. The triangle inequality is the tool behind the a posteriori bound (4.23) in the proof of Theorem 4.2.
--
--   **Formalization Note** The book states "distance" and spells out the triangle inequality and the zero set; nonnegativity and symmetry, which "distance" includes, are stated explicitly.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Remark 4.12, p. 439

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

namespace CompOT.Sinkhorn

/-- Remark 4.12, p. 439: `d_H` is a distance on the projective cone of positive vectors:
it is nonnegative and symmetric, satisfies the triangle inequality, and
`d_H(u, u') = 0` if and only if `u = r u'` for some `r > 0`. -/
theorem remark_4_12_distance {n : ℕ} (hn : 0 < n) (u u' u'' : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (hu' : ∀ i, 0 < u' i) (hu'' : ∀ i, 0 < u'' i) :
    0 ≤ hilbertMetric u u' ∧
    hilbertMetric u u' = hilbertMetric u' u ∧
    hilbertMetric u u'' ≤ hilbertMetric u u' + hilbertMetric u' u'' ∧
    (hilbertMetric u u' = 0 ↔ ∃ r : ℝ, 0 < r ∧ u = r • u') := by sorry

end CompOT.Sinkhorn
