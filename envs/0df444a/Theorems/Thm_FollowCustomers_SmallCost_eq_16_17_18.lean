-- Prove2me | Theorems.Thm_FollowCustomers_SmallCost_eq_16_17_18
-- name    : FollowCustomers.SmallCost.eq_16_17_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:50.631743+00:00
-- url     : https://prove2.me/theorems/d331e137-2a07-4e78-85b8-15f56e8832ff
-- title:
--   (16)–(18), p. 14 (PDF 16) — two-term expansions: x*, x̲ = 1/2 + ∛(9σ²/(4δ))K^{1/3} ± ½∛(δσ⁴/18)K^{2/3} + o(K^{2/3})
-- statement:
--   Let $r,\sigma^2,\delta>0$ and let $K\mapsto(\underline x(K),x^*(K))$ be a solution branch of (14)–(15). Write $a=\sqrt[3]{9\sigma^2/(4\delta)}$ and $b=\sqrt[3]{\delta\sigma^4/18}$. Then, as $K\to0^+$,
--   $$\frac{x^*-\tfrac12-aK^{1/3}}{K^{2/3}}\to\frac b2,\qquad \frac{\underline x-\tfrac12-aK^{1/3}}{K^{2/3}}\to-\frac b2,\qquad \frac{x^*-\underline x}{K^{2/3}}\to b .$$
--   Equivalently,
--   $$x^*=\tfrac12+aK^{1/3}+\tfrac b2K^{2/3}+o(K^{2/3}),\qquad \underline x=\tfrac12+aK^{1/3}-\tfrac b2K^{2/3}+o(K^{2/3}).$$
--
--   These are the paper's equations (16)–(18). The leading coefficient $a$ increases with $\sigma^2$ and decreases with $\delta$, the gap coefficient $b$ increases with both, and neither depends on $r$; these facts are the content of Proposition 2.
--
--   **Formalization Note.** The paper prints (16)–(17) as $(x^*-\tfrac12)/K^{1/3}\to a+\tfrac b2K^{1/3}$, whose right side still depends on $K$, so it is not a limit statement as written. It is read here as the two-term expansion above, which is what the appendix derivation from (xv)–(xvii), (xix) and (xx) gives. Equation (18) is a genuine limit and is stated as printed. The powers $K^{1/3}$, $K^{2/3}$ and the cube roots are real powers of positive numbers.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), p. 14 (PDF 16), (16)–(18); Appendix p. 31 (PDF 33), (xv)–(xvii)

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

namespace FollowCustomers.SmallCost

/-- (16)–(18), p. 14, read as two-term expansions: on every solution branch, as `K → 0⁺`,
`x* = 1/2 + ∛(9σ²/(4δ)) K^{1/3} + ½∛(δσ⁴/18) K^{2/3} + o(K^{2/3})`,
`x̲ = 1/2 + ∛(9σ²/(4δ)) K^{1/3} − ½∛(δσ⁴/18) K^{2/3} + o(K^{2/3})`, and
`(x* − x̲)/K^{2/3} → ∛(δσ⁴/18)`. -/
theorem eq_16_17_18 (P : Params) (xl xs : ℝ → ℝ) (hP : P.Standing) (hb : IsBranch P xl xs) :
    Tendsto (fun K => (xs K - 1 / 2 - coefA P * K ^ ((1 : ℝ) / 3)) / K ^ ((2 : ℝ) / 3))
        (𝓝[>] 0) (𝓝 (coefB P / 2)) ∧
      Tendsto (fun K => (xl K - 1 / 2 - coefA P * K ^ ((1 : ℝ) / 3)) / K ^ ((2 : ℝ) / 3))
        (𝓝[>] 0) (𝓝 (-(coefB P / 2))) ∧
      Tendsto (fun K => (xs K - xl K) / K ^ ((2 : ℝ) / 3)) (𝓝[>] 0) (𝓝 (coefB P)) := by sorry

end FollowCustomers.SmallCost
