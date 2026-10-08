-- Prove2me | Theorems.Thm_BootRobust_Optimality_inf_N_lt
-- name    : BootRobust.Optimality.inf_N_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:43.699179+00:00
-- url     : https://prove2.me/theorems/2b5dcfe9-9bca-41ec-b355-983412b52e75
-- title:
--   B.2, p. 27 — inf_{D′ ∈ 𝒩} B(D′, D_tr) < r for an open 𝒩 ∋ D with B(D, D_tr) = r
-- statement:
--   Let $D,D_{\rm tr}\in\mathcal D_n$ with $D_{\rm tr}$ having all coordinates positive, and suppose $B(D,D_{\rm tr})=r$ with $r>0$. Let $\mathcal N\subseteq\mathcal D_n$ be open in $\mathcal D_n$ with $D\in\mathcal N$. Then
--   $$\inf_{D'\in\mathcal N}B(D',D_{\rm tr})<r.$$
--
--   Combined with Sanov's lower bound (31) and the inclusion $\mathcal N\subseteq\mathcal R$, this gives the strict rate inequality of Proposition 1.
--
--   **Formalization Note** The infimum is taken in the extended reals. The hypothesis $r>0$ is a disclosed addition: for $r=0$ the strict inequality is false since $B\ge 0$. In Proposition 1 it holds automatically, because $B(D,D_{\rm tr})=0$ forces $D=D_{\rm tr}$ while $R(D_{\rm tr},D_{\rm tr})=0$ contradicts $R>r$ on $\mathcal N\ni D$.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, B.2 (proof of Proposition 1), p. 27, "Hence, indeed we have …"

import Mathlib
import Definitions.Def_BootRobust_Optimality_Setting

namespace BootRobust.Optimality

/-- B.2, p. 27: if `B(D, D_tr) = r > 0` and `N` is a relatively open subset of `𝒟ₙ` containing `D`,
then `inf_{D' ∈ N} B(D', D_tr) < r`. -/
theorem inf_N_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D Dtr : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (r : ℝ) (hB : BootRobust.Perf.bootDist D Dtr = (r : EReal)) (hr : 0 < r)
    (N : Set (ι → ℝ)) (hN : relOpen N) (hDN : D ∈ N) :
    ⨅ D' ∈ N, BootRobust.Perf.bootDist D' Dtr < (r : EReal) := by sorry

end BootRobust.Optimality
