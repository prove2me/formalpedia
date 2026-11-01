-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_theorem_2_positive_cost
-- name    : CohenPriceFairness.LocalWelfare.theorem_2_positive_cost
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T00:35:27.489908+00:00
-- url     : https://prove2.me/theorems/7f17f5e3-d722-4859-8851-83eed3bca1a0
-- title:
--   Theorem 2 — a little fairness raises welfare under price and no-purchase valuation fairness, lowers it under demand and surplus fairness
-- statement:
--   This is Theorem 2 of Cohen, Elmachtoub and Lei, *Price Discrimination with Fairness Constraints* (Management Science, 2022, §2.3, p. 7). It is stated here on the parameter range in which the paper's proof is carried out.
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
--   1. (linear demand) $V_i\sim U(0,b_i)$ with $b_0\ne b_1$ and $0<c<\min\{b_0,b_1\}$;
--   2. (exponential demand) $V_i\sim\mathrm{Exp}(\lambda_i)$ with $\lambda_0\ne\lambda_1$ and $c>0$.
--
--   Then unconstrained optimal prices exist. For every choice of them, and every selection of optimal prices under a small amount of fairness,
--
--   $$
--   \mathcal W'(0)>0\ \text{ under price or no-purchase valuation fairness},\qquad
--   \mathcal W'(0)<0\ \text{ under demand or surplus fairness}.
--   $$
--
--   In words: when a seller that price-discriminates is required to close a small fraction of its fairness gap, social welfare rises if fairness is measured by prices or by the valuations of non-buyers, and falls if it is measured by purchase probabilities or by consumer surplus. This is the central result of §2.3 and the goal of the mission.
--
--   **Relation to the printed statement.** The printed theorem places no restriction on the cost beyond the model's $c\ge0$ (p. 4). Its proof (Online Appendix A, p. 33) substitutes the closed forms of Table 3 (p. 34), such as $p_i^*=(b_i+c)/2$, into Lemma 1 and uses the strict orderings $p_0^*<p_1^*$, $\bar F_0(p_0^*)<\bar F_1(p_1^*)$, $S_0(p_0^*)<S_1(p_1^*)$ and $N_0(p_0^*)<N_1(p_1^*)$. The closed forms require $c<\min\{b_0,b_1\}$, the standing assumption $c<b_0<b_1$ of §3 (p. 7), and all four orderings are strict once $c>0$. At $c=0$ the demand ordering becomes an equality: both groups buy with the same probability at their optimal prices ($1/2$ for uniform, $e^{-1}$ for exponential valuations), so the demand-fairness constraint never binds and $\mathcal W'(0)=0$; the other three signs remain strict. For uniform valuations with $c\ge\min_i b_i$, the lower-valuation group is not served even without a fairness constraint. A version with weak inequalities that also covers $c=0$ is a separate milestone of this mission.
--
--   **Differences from the source.**
--   - The cost range $0<c<\min\{b_0,b_1\}$ (uniform) or $c>0$ (exponential) is stated in the theorem. The printed statement leaves it to the proof and to §3, as explained above.
--   - The total-surplus formula on pp. 5 and 7 prints $d_0S_1(p_0(\alpha))+d_1S_1(p_1(\alpha))$; the group-specific index $d_0S_0+d_1S_1$ of p. 4 and Online Appendix p. 31 is used.
--   - $N_i(p)$ is undefined when no customer has valuation below $p$ (for example at $p=0$); it is set to $0$ there, the right-continuous extension for both families.
--
--   **Formalization Note.** Valuation laws are Borel probability measures on $\mathbb R$: the uniform law on $[0,b]$ is normalized Lebesgue measure and the exponential law is Mathlib's `expMeasure`. Optimality is stated by comparison with every feasible price pair, never through a supremum. Because the paper does not specify a tie-breaking rule, the statement covers every unconstrained optimum $(p_0^*,p_1^*)$ and every selection of constrained optima $\alpha\mapsto(p_0(\alpha),p_1(\alpha))$ on some interval $[0,\varepsilon]$ that starts at that optimum. It asserts that such a selection exists and that, for each one, the finite right derivative exists and has the stated sign. No continuity or differentiability of the optimal price path is assumed.
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article (Articles in Advance, pp. 1-17) and its Online Appendix (mnsc.2022.4317.sm1); Theorem 2, §2.3, p. 7; model §2, pp. 4-5; standing assumption c < b0 < b1, §3, p. 7; proof: Online Appendix A, p. 33, with Table 3, p. 34.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

open MeasureTheory ProbabilityTheory

namespace CohenPriceFairness.LocalWelfare

/-- Theorem 2 (p. 7) on the cost range of its proof (Online Appendix A, p. 33, Table 3):
`0 < c < min b₀ b₁` for uniform valuations, `0 < c` for exponential valuations. -/
theorem theorem_2_positive_cost (m : Market) (hd : ∀ i, 0 < m.population i)
    (hc : 0 < m.cost)
    (hf : (∃ b : Fin 2 → ℝ, (∀ i, 0 < b i) ∧ b 0 ≠ b 1 ∧ m.cost < min (b 0) (b 1) ∧
            ∀ i, m.law i = uniformLaw (b i)) ∨
          (∃ rate : Fin 2 → ℝ, (∀ i, 0 < rate i) ∧ rate 0 ≠ rate 1 ∧
            ∀ i, m.law i = expMeasure (rate i))) :
    (∃ b : Prices, BaselineOptimal m b) ∧
    ∀ b : Prices, BaselineOptimal m b →
      SensitivityClaim m b .price (fun D => 0 < D) ∧
      SensitivityClaim m b .nonbuyer (fun D => 0 < D) ∧
      SensitivityClaim m b .demand (fun D => D < 0) ∧
      SensitivityClaim m b .surplus (fun D => D < 0) := by sorry

end CohenPriceFairness.LocalWelfare
