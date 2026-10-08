-- Prove2me | Theorems.Thm_BootRobust_Optimality_bootDist_segment_le
-- name    : BootRobust.Optimality.bootDist_segment_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:07.71758+00:00
-- url     : https://prove2.me/theorems/980bca6f-fe9c-4f31-b76d-71fbc620379b
-- title:
--   B.2, p. 27 — B(D(λ), D_tr) ≤ λB(D, D_tr) + (1−λ)B(D_tr, D_tr) < r along D(λ) = λD + (1−λ)D_tr
-- statement:
--   Let $D,D_{\rm tr}\in\mathcal D_n$ with $D_{\rm tr}$ having all coordinates positive, let $\lambda\in[0,1]$ and $D(\lambda)=\lambda D+(1-\lambda)D_{\rm tr}$. Then
--   1. $B(D(\lambda),D_{\rm tr})\le\lambda\,B(D,D_{\rm tr})+(1-\lambda)\,B(D_{\rm tr},D_{\rm tr})$;
--   2. $B(D_{\rm tr},D_{\rm tr})=0$;
--   3. if moreover $B(D,D_{\rm tr})=r$ with $r>0$ and $\lambda\in(0,1)$, then
--   $$B(D(\lambda),D_{\rm tr})<r.$$
--
--   This is the convexity step of the proof of Proposition 1: moving from $D$ towards $D_{\rm tr}$ strictly lowers the bootstrap distance below $r$.
--
--   **Formalization Note** $B$ is extended-real valued; with $D_{\rm tr}>0$ every value here is finite. The condition $r>0$ in item 3 is needed for the strict inequality and holds in Proposition 1.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, B.2 (proof of Proposition 1), p. 27, "From convexity of B we have …"

import Mathlib
import Definitions.Def_BootRobust_Optimality_Setting

namespace BootRobust.Optimality

/-- B.2, p. 27, the convexity step: along the segment `D(λ) = λ D + (1 - λ) D_tr`, `λ ∈ [0, 1]`,
`B(D(λ), D_tr) ≤ λ B(D, D_tr) + (1 - λ) B(D_tr, D_tr)`, and `B(D_tr, D_tr) = 0`; hence, if
`B(D, D_tr) = r` with `r > 0` and `λ ∈ (0, 1)`, then `B(D(λ), D_tr) < r`. -/
theorem bootDist_segment_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D Dtr : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    BootRobust.Perf.bootDist (lam • D + (1 - lam) • Dtr) Dtr ≤
        (lam : EReal) * BootRobust.Perf.bootDist D Dtr + ((1 - lam : ℝ) : EReal) * BootRobust.Perf.bootDist Dtr Dtr ∧
      BootRobust.Perf.bootDist Dtr Dtr = 0 ∧
      ∀ r : ℝ, BootRobust.Perf.bootDist D Dtr = (r : EReal) → 0 < r → lam ∈ Set.Ioo (0 : ℝ) 1 →
        BootRobust.Perf.bootDist (lam • D + (1 - lam) • Dtr) Dtr < (r : EReal) := by sorry

end BootRobust.Optimality
