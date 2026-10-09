-- Prove2me | Theorems.Thm_BootRobust_NWDual_lemma_2
-- name    : BootRobust.NWDual.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:23.514604+00:00
-- url     : https://prove2.me/theorems/0566e2d1-10c4-47fe-bfa5-20617d75dfee
-- title:
--   Lemma 2, pp. 17–18 — the bootstrap robust Nadaraya–Watson budget equals inf{α : ∃ν > 0, ν log Σ D·exp((L−α)w/ν) + rν ≤ 0}
-- statement:
--   Let $\Omega_n$ be a finite support, $D\in\mathcal D_n$ any distribution on it (zeros allowed), $r\in\mathbb R$ a radius, $w_i=w_n(\bar x_i,x_0)>0$ positive weights, and $\bar z$ a fixed decision with losses $L(\bar z,\bar y_i)$. Let $B$ be the bootstrap distance (27). Then the bootstrap robust Nadaraya–Watson cost with $k(n)=n$,
--   $$c_n(\bar z,D,x_0)=\sup\Big\{\frac{\sum_iw_i\,L(\bar z,\bar y_i)\,D'_i}{\sum_iw_i\,D'_i}:\ D'\in\mathcal D_n,\ B(D',D)\le r\Big\},$$
--   equals the optimal value of the dual convex program (33):
--   $$c_n(\bar z,D,x_0)=\inf\Big\{\alpha\in\mathbb R:\ \exists\,\nu>0,\ \ \nu\log\Big(\sum_{i}\exp\Big(\frac{(L(\bar z,\bar y_i)-\alpha)\,w_i}{\nu}\Big)D_i\Big)+r\nu\le0\Big\}.$$
--
--   The dual replaces a supremum over the $|\Omega_n|$-dimensional ambiguity set by a two-variable exponential-cone program, so that minimizing the robust budget over $\bar z$ becomes a single convex program in $(\bar z,\alpha,\nu)$.
--
--   **Formalization Note** Both sides are extended reals. The equality is stated for every real $r$, as on the page: for $r<0$ the ball is empty and both sides are $-\infty$; for $r=0$ both equal the nominal estimate at $D$. The page's $\nu\in\mathbb R_+$ is replaced by $\nu>0$, since at $\nu=0$ Lean's division by zero would make every $\alpha$ feasible; the infimum over $\alpha$ is unchanged. $B(D',D)=+\infty$ whenever $D'$ charges a zero of $D$. Losses are real-valued (the paper allows $+\infty$), and only the losses of the fixed decision enter.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, Lemma 2 and (33), pp. 17–18 (proof B.8, pp. 31–32)

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

namespace BootRobust.NWDual

/-- Lemma 2, pp. 17–18: for every `D ∈ Dₙ` and every radius `r`, the bootstrap robust (`R = B`)
Nadaraya–Watson budget (24) with `k(n) = n` equals the infimum of `α` over the dual program (33). -/
theorem lemma_2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (r : ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) {Z : Type*} (L : Z → ι → ℝ) (z : Z) :
    robustNW BootRobust.Perf.bootDist D r w (L z) = ⨅ α ∈ dualSet D r w (L z), (α : EReal) := by sorry

end BootRobust.NWDual
