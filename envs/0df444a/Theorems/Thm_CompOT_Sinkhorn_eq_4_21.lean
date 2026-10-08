-- Prove2me | Theorems.Thm_CompOT_Sinkhorn_eq_4_21
-- name    : CompOT.Sinkhorn.eq_4_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:59.550005+00:00
-- url     : https://prove2.me/theorems/a41eb7ca-c852-4fe1-ae5b-3e96996e4e93
-- title:
--   (4.21), Remark 4.12, p. 439 — d_H(u, u′) = ‖log u − log u′‖_var
-- statement:
--   Let $n \ge 1$ and let $u, u' \in \mathbb{R}^n$ have positive entries. Hilbert's projective metric $d_{\mathcal H}(u,u') = \log \max_{i,j} \frac{u_i u'_j}{u_j u'_i}$ equals the variation seminorm of the difference of the logarithms:
--   $$d_{\mathcal H}(u,u') = \big\|\log(u) - \log(u')\big\|_{\mathrm{var}}, \qquad \|f\|_{\mathrm{var}} = (\max_i f_i) - (\min_i f_i),$$
--   where $\log$ is applied entrywise.
--
--   By this logarithmic change of variables the Hilbert metric on rays of the positive cone becomes a seminorm that vanishes exactly on constant vectors; it turns rates in $d_{\mathcal H}$ for Sinkhorn's scalings into rates for the dual potentials $\varepsilon \log u$.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Remark 4.12, (4.21), p. 439

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

namespace CompOT.Sinkhorn

/-- (4.21), Remark 4.12, p. 439: after a logarithmic change of variables, Hilbert's
projective metric is the variation seminorm,
`d_H(u, u') = ‖log u − log u'‖_var`. -/
theorem eq_4_21 {n : ℕ} (hn : 0 < n) (u u' : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (hu' : ∀ i, 0 < u' i) :
    hilbertMetric u u' = varNorm (fun i => Real.log (u i) - Real.log (u' i)) := by sorry

end CompOT.Sinkhorn
