-- Prove2me | Theorems.Thm_BootRobust_Perf_partialEst_eq_ratio
-- name    : BootRobust.Perf.partialEst_eq_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:14.918972+00:00
-- url     : https://prove2.me/theorems/53b869f8-e5aa-41b4-bada-1d8e187db9ac
-- title:
--   B.1, p. 26 — on D^j_n the partial estimator (22) is the weighted average of the loss over N^j_n(x₀)
-- statement:
--   Let $n\ge 1$, $k\ge 1$, let $N^0,N^1,\dots$ be neighbourhoods in $\Omega_n$, $w>0$ weights and $\ell$ losses. For every $j$ and every distribution $D\in\mathcal D^j_n$, the partial estimator of (22) is
--   $$E^{n,j}_D=\frac{\sum_{i\in N^j}\ell_i\,w_i\,D_i}{\sum_{i\in N^j}w_i\,D_i}.$$
--
--   The only feasible scale in (22) is $s=1/\sum_{i\in N^j}w_iD_i$, so the supremum is attained at a single point. This closed form is the bridge between the linear-programming description and the weighted-average estimator (18).
--
--   **Formalization Note** The page states the identity for $D\in\mathcal D^j_{n,n}=\mathcal D^j_n\cap\mathcal D_{n,n}$; it is stated here on all of $\mathcal D^j_n$, which is more general. The page's "$s=1/\sum w_n P$" is a misprint for $1/\sum w_n D$.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, B.1 (proof of Theorem 1), p. 26, "Notice also that the only feasible s …"

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Perf

/-- B.1, p. 26: on `D^j_n` the partial estimator (22) is the `w`-weighted average of the loss
over the neighbourhood `N^j`. -/
theorem partialEst_eq_ratio {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (N : ℕ → Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (ℓ : ι → ℝ) (j : ℕ)
    (D : ι → ℝ) (hD : D ∈ Dj n k N j) :
    partialEst n k N w ℓ j D =
      (((∑ i ∈ N j, ℓ i * w i * D i) / (∑ i ∈ N j, w i * D i) : ℝ) : EReal) := by sorry

end BootRobust.Perf
