-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_lemma_1_nondegenerate
-- name    : CohenPriceFairness.LocalWelfare.lemma_1_nondegenerate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T00:35:46.374769+00:00
-- url     : https://prove2.me/theorems/2b42a7eb-ae0f-4aa5-afbe-8643a0517e3f
-- title:
--   Lemma 1 — welfare sensitivity under the four fairness measures, at a nondegenerate optimum
-- statement:
--   This is Lemma 1 of the Online Appendix of Cohen, Elmachtoub and Lei (2022, Appendix A, pp. 30–31). It gives, for a general valuation distribution, an exact criterion for the sign of the welfare effect of a little fairness. The proof of Theorem 2 applies it to linear and exponential demand.
--
--   **Setting.** Two groups $i\in\{0,1\}$ have positive masses $d_i$, nonnegative valuations $V_i$ with finite mean, and a common cost $c\ge0$. Purchase probability $\bar F_i$, profit $R_i(p)=d_i(p-c)\bar F_i(p)$, surplus $S_i(p)=\mathbb E[(V_i-p)^+]$, no-purchase valuation $N_i$, Problem (1) and $\mathcal W'(0)$ are as in the main paper (§2 and §2.3, pp. 4–7). Let $p_i^*$ maximize $R_i$ over $p\ge0$.
--
--   **Hypotheses.**
--
--   1. (Lemma 1, as printed) $\bar F_i$, $S_i$, $N_i$ and $R_i$ are continuous and twice differentiable at $p_i^*$, and $\bar F_i$, $S_i$, $N_i$ are monotone and invertible near $p_i^*$.
--   2. (Nondegenerate optimum) $p_i^*$ is the unique maximizer of $R_i$ on $[0,\infty)$, and $R_i''(p_i^*)<0$.
--   3. (Nonzero slopes) In part (b), $\bar F_i'(p_i^*)\ne0$; in part (d), $N_i'(p_i^*)\ne0$.
--
--   Write $q_i=\bar F_i(p_i^*)$ and $r_i=R_i''(p_i^*)$. Then a selection of optimal prices under a small amount of fairness exists, every such selection has a finite $\mathcal W'(0)$, and:
--
--   1. (Price fairness) If $p_0^*<p_1^*$, then $\mathcal W'(0)>0 \iff d_1q_1r_0-d_0q_0r_1<0$.
--   2. (Demand fairness) If $q_0<q_1$, then $\mathcal W'(0)>0 \iff d_1q_1\bar F_1'(p_1^*)\,r_0-d_0q_0\bar F_0'(p_0^*)\,r_1<0$.
--   3. (Surplus fairness) If $S_0(p_0^*)<S_1(p_1^*)$, then $\mathcal W'(0)>0 \iff d_1q_1^2\,r_0-d_0q_0^2\,r_1>0$.
--   4. (No-purchase valuation fairness) If $N_0(p_0^*)<N_1(p_1^*)$, then $\mathcal W'(0)>0 \iff d_1q_1N_1'(p_1^*)\,r_0-d_0q_0N_0'(p_0^*)\,r_1<0$.
--
--   The lemma reduces the welfare effect of a little fairness to the local data $q_i$, $r_i$ and the slope of the fairness measure at the unconstrained optimum. This is how Theorem 2 is obtained for linear and exponential demand from the closed forms of Table 3.
--
--   **Differences from the source.**
--   - Hypotheses 2 and 3 are not printed in the lemma but are used in its proof. The proof treats $p_i(\alpha)$ as a function with $p_i(0)=p_i^*$ that is differentiable at $0$, which presumes a unique optimum. Eq. (11) (p. 32) divides by $R_0''(p_0^*)+R_1''(p_1^*)$. Part (b) (pp. 32–33) divides by $\bar F_1'(p_1^*)$ and uses $(\bar F_0^{-1})'=1/\bar F_0'$; part (d) is proved "similarly". Without them the criterion can fail. With two distinct maximizers of $R_0$, a constrained optimum can jump to the other one. With $R_i''(p_i^*)=0$, price changes are no longer of order $\alpha$. The earlier formalization of this lemma omitted them and was disproved by a distribution whose profit has two maximizers. That counterexample lies outside the setting the proof addresses.
--   - "Monotone and invertible" is read locally, on an open interval around $p_i^*$, because uniform demand is flat outside its support.
--   - The total-surplus formula on pp. 5 and 7 prints $d_0S_1(p_0(\alpha))+d_1S_1(p_1(\alpha))$; the group-specific index $d_0S_0+d_1S_1$ of p. 4 and Online Appendix p. 31 is used.
--   - $N_i(p)$ is undefined when no customer has valuation below $p$ (for example at $p=0$); it is set to $0$ there, the right-continuous extension for both families.
--
--   **Formalization Note.** Valuation laws are Borel probability measures on $\mathbb R$: the uniform law on $[0,b]$ is normalized Lebesgue measure and general laws are only required to be nonnegative with finite mean. Optimality is stated by comparison with every feasible price pair, never through a supremum. Because the paper does not specify a tie-breaking rule, the statement covers every unconstrained optimum $(p_0^*,p_1^*)$ and every selection of constrained optima $\alpha\mapsto(p_0(\alpha),p_1(\alpha))$ on some interval $[0,\varepsilon]$ that starts at that optimum. It asserts that such a selection exists and that, for each one, the finite right derivative exists and has the stated sign. No continuity or differentiability of the optimal price path is assumed.
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article (Articles in Advance, pp. 1-17) and its Online Appendix (mnsc.2022.4317.sm1); Online Appendix A, Lemma 1(a)-(d), pp. 30-31; proof pp. 31-33 (Eq. (11), p. 32; part (b), pp. 32-33); model §2, pp. 4-5.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity

namespace CohenPriceFairness.LocalWelfare

/-- Lemma 1(a)–(d) (Online Appendix A, pp. 30–31), with the nondegeneracy used in its proof
(pp. 31–33) made explicit: unique unconstrained optima, strictly negative profit curvature,
and nonzero demand / no-purchase-valuation slopes where the proof divides by them. -/
theorem lemma_1_nondegenerate (m : Market) (hm : m.Admissible) (b : Prices)
    (hb : BaselineOptimal m b) (hr : LemmaRegularity m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i)
    (hcurv : ∀ i, deriv (deriv (profit m i)) (b i) < 0) :
    (b 0 < b 1 → SensitivityClaim m b .price (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (deriv (profit m 1)) (b 1) < 0))) ∧
    (demand m 0 (b 0) < demand m 1 (b 1) → (∀ i, deriv (demand m i) (b i) ≠ 0) →
      SensitivityClaim m b .demand (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (demand m 1) (b 1) *
          deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (demand m 0) (b 0) *
          deriv (deriv (profit m 1)) (b 1) < 0))) ∧
    (surplus m 0 (b 0) < surplus m 1 (b 1) → SensitivityClaim m b .surplus (fun D =>
      (0 < D ↔
        m.population 1 * (demand m 1 (b 1)) ^ 2 * deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * (demand m 0 (b 0)) ^ 2 * deriv (deriv (profit m 1)) (b 1) > 0))) ∧
    (nonbuyer m 0 (b 0) < nonbuyer m 1 (b 1) → (∀ i, deriv (nonbuyer m i) (b i) ≠ 0) →
      SensitivityClaim m b .nonbuyer (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (nonbuyer m 1) (b 1) *
          deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (nonbuyer m 0) (b 0) *
          deriv (deriv (profit m 1)) (b 1) < 0))) := by sorry

end CohenPriceFairness.LocalWelfare
