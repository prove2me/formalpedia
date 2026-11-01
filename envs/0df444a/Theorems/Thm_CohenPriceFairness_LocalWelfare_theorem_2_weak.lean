-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_theorem_2_weak
-- name    : CohenPriceFairness.LocalWelfare.theorem_2_weak
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T00:35:53.574733+00:00
-- url     : https://prove2.me/theorems/e8e35f3e-9428-4e49-a912-e2993698154e
-- title:
--   Theorem 2 (weak-inequality form) — the welfare signs hold weakly down to zero cost
-- statement:
--   This is the weak-inequality form of Theorem 2 of Cohen, Elmachtoub and Lei (2022, §2.3, p. 7). It extends the mission goal to zero marginal cost, where one of the strict signs becomes an equality.
--
--   **Model** (§2, pp. 4–5). A seller with unlimited supply and common marginal cost $c\ge0$ sells one product to two customer groups $i\in\{0,1\}$ with positive population masses $d_i$. A customer of group $i$ has a random valuation $V_i$ and buys at price $p\ge0$ exactly when $V_i\ge p$. For each group write
--
--   - $\bar F_i(p)=\Pr(V_i\ge p)$ for the purchase probability (market share),
--   - $R_i(p)=d_i\,(p-c)\,\bar F_i(p)$ for the profit,
--   - $S_i(p)=\mathbb E\big[(V_i-p)^+\big]$ for the normalized consumer surplus,
--   - $N_i(p)=\mathbb E[V_i\mid V_i<p]$ for the no-purchase valuation (taken to be $0$ when $\Pr(V_i<p)=0$),
--
--   and let $p_i^*$ be an unconstrained optimal price, i.e. a maximizer of $R_i$ over $p\ge0$.
--
--   A fairness measure $M_i$ is one of $p$ (price), $\bar F_i$ (demand), $S_i$ (surplus) or $N_i$ (no-purchase valuation). For a fairness level $\alpha\in[0,1]$ the seller solves Problem (1):
--
--   $$
--   \max_{p_0,\,p_1\ge0}\ R_0(p_0)+R_1(p_1)
--   \quad\text{s.t.}\quad
--   |M_0(p_0)-M_1(p_1)|\le(1-\alpha)\,|M_0(p_0^*)-M_1(p_1^*)|.
--   $$
--
--   If $p_0(\alpha),p_1(\alpha)$ are optimal prices, the social welfare is $\mathcal W(\alpha)=\sum_{i}\big[R_i(p_i(\alpha))+d_i\,S_i(p_i(\alpha))\big]$, and its right derivative at zero (footnote 7) is
--
--   $$
--   \mathcal W'(0)=\lim_{\alpha\downarrow0}\frac{\mathcal W(\alpha)-\mathcal W(0)}{\alpha}.
--   $$
--
--   **Theorem.** Suppose that one of the following holds:
--
--   1. (linear demand) $V_i\sim U(0,b_i)$ with $b_0\ne b_1$ and $0\le c<\min\{b_0,b_1\}$;
--   2. (exponential demand) $V_i\sim\mathrm{Exp}(\lambda_i)$ with $\lambda_0\ne\lambda_1$ and $c\ge0$.
--
--   Then unconstrained optimal prices exist. For every choice of them, and every selection of optimal prices under a small amount of fairness, the finite right derivative $\mathcal W'(0)$ exists and
--
--   $$
--   \mathcal W'(0)\ge0\ \text{ under price or no-purchase valuation fairness},\qquad
--   \mathcal W'(0)\le0\ \text{ under demand or surplus fairness}.
--   $$
--
--   The mission goal gives the strict signs for $c>0$. This item adds the boundary $c=0$, so the direction of the welfare effect in Theorem 2 does not reverse anywhere on the range in which both groups are served. At $c=0$ only the demand-fairness sign degenerates: both groups buy with the same probability at their optimal prices ($1/2$ for uniform, $e^{-1}$ for exponential valuations), so the demand-fairness constraint never binds and $\mathcal W'(0)=0$.
--
--   The weak form does not extend to uniform costs above both supports, a case the paper excludes through the standing assumption $c<b_0<b_1$ of §3 (p. 7). There no group is served at the unconstrained optimum. The no-purchase valuation $N_i(p)=\min\{p,b_i\}/2$ cannot be raised above $b_i/2$, so narrowing its gap forces the seller to sell below cost. For example, with $d_0=d_1=1$, $b_0=1$, $b_1=2$ and $c=3$, no-purchase valuation fairness gives $\mathcal W'(0)=-1/2$.
--
--   **Differences from the source.**
--   - The printed theorem asserts strict inequalities and imposes no restriction on the cost beyond the model's $c\ge0$ (p. 4). This item weakens each sign to a non-strict inequality and keeps the cost range $0\le c<\min\{b_0,b_1\}$ (uniform) or $c\ge0$ (exponential), as explained above.
--   - The total-surplus formula on pp. 5 and 7 prints $d_0S_1(p_0(\alpha))+d_1S_1(p_1(\alpha))$; the group-specific index $d_0S_0+d_1S_1$ of p. 4 and Online Appendix p. 31 is used.
--   - $N_i(p)$ is undefined when no customer has valuation below $p$ (for example at $p=0$); it is set to $0$ there, the right-continuous extension for both families.
--
--   **Formalization Note.** Valuation laws are Borel probability measures on $\mathbb R$: the uniform law on $[0,b]$ is normalized Lebesgue measure and the exponential law is Mathlib's `expMeasure`. Optimality is stated by comparison with every feasible price pair, never through a supremum. Because the paper does not specify a tie-breaking rule, the statement covers every unconstrained optimum $(p_0^*,p_1^*)$ and every selection of constrained optima $\alpha\mapsto(p_0(\alpha),p_1(\alpha))$ on some interval $[0,\varepsilon]$ that starts at that optimum. It asserts that such a selection exists and that, for each one, the finite right derivative exists and has the stated sign. No continuity or differentiability of the optimal price path is assumed.
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article (Articles in Advance, pp. 1-17) and its Online Appendix (mnsc.2022.4317.sm1); Theorem 2, §2.3, p. 7, with non-strict signs and cost range 0 <= c < min(b0, b1) (uniform) or c >= 0 (exponential); model §2, p. 4; standing assumption c < b0 < b1, §3, p. 7; proof of Theorem 2: Online Appendix A, p. 33.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

open MeasureTheory ProbabilityTheory

namespace CohenPriceFairness.LocalWelfare

/-- Theorem 2 (p. 7) with non-strict signs, on the cost range of its proof extended to `c = 0`:
`0 ≤ c < min b₀ b₁` for uniform valuations, `0 ≤ c` for exponential valuations. -/
theorem theorem_2_weak (m : Market) (hd : ∀ i, 0 < m.population i)
    (hc : 0 ≤ m.cost)
    (hf : (∃ b : Fin 2 → ℝ, (∀ i, 0 < b i) ∧ b 0 ≠ b 1 ∧ m.cost < min (b 0) (b 1) ∧
            ∀ i, m.law i = uniformLaw (b i)) ∨
          (∃ rate : Fin 2 → ℝ, (∀ i, 0 < rate i) ∧ rate 0 ≠ rate 1 ∧
            ∀ i, m.law i = expMeasure (rate i))) :
    (∃ b : Prices, BaselineOptimal m b) ∧
    ∀ b : Prices, BaselineOptimal m b →
      SensitivityClaim m b .price (fun D => 0 ≤ D) ∧
      SensitivityClaim m b .nonbuyer (fun D => 0 ≤ D) ∧
      SensitivityClaim m b .demand (fun D => D ≤ 0) ∧
      SensitivityClaim m b .surplus (fun D => D ≤ 0) := by sorry

end CohenPriceFairness.LocalWelfare
