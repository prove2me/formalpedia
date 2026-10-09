-- Prove2me | Theorems.Thm_BalancedPrices_Extension_theorem_3_2
-- name    : BalancedPrices.Extension.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:36.705523+00:00
-- url     : https://prove2.me/theorems/42a29781-6add-402d-8f96-b9bd0b121152
-- title:
--   Theorem 3.2, p. 549 — posting δ·E_ṽ[p^ṽ] with δ = α/(1 + αβ) earns welfare ≥ 1/(1 + αβ)·E_v[v(ALG(v))]
-- statement:
--   Let there be $n$ agents; agent $i$ has an outcome space $X_i$ with a null outcome $\varnothing$, and the feasible outcome profiles form a downward-closed set $\mathcal F\subseteq X_1\times\dots\times X_n$. Agent $i$'s type $v_i$ is drawn independently from a distribution $\mathcal D_i$ on a countable set $V_i$, and a type values each outcome in $[0,1]$. Let $\mathrm{ALG}$ be an outcome rule with $\mathrm{ALG}(\mathbf v)\in\mathcal F$ for every type profile $\mathbf v$, and let $\alpha>0$, $\beta\ge0$.
--
--   For every type profile $\tilde{\mathbf v}$ let $p^{\tilde{\mathbf v}}$ be a pricing rule (prices in $[0,\infty]$, $\infty$ for outcomes that cannot be feasibly added, $0$ for the null outcome at feasible partial allocations), and suppose the collection $(p^{\tilde{\mathbf v}})_{\tilde{\mathbf v}}$ is $(\alpha,\beta)$-balanced with respect to $\mathrm{ALG}$ and the index order: there is one exchange-compatible family $(\mathcal F_{\mathbf x})_{\mathbf x\in X}$ such that each $p^{\tilde{\mathbf v}}$ is $(\alpha,\beta)$-balanced for $\tilde{\mathbf v}$ with respect to $\mathrm{ALG}$ and $(\mathcal F_{\mathbf x})$ (Definition 3.1).
--
--   Post the prices $\delta p$, where
--   $$p_i(x_i\mid\mathbf y)=\mathbb E_{\tilde{\mathbf v}\sim\mathcal D}\bigl[p^{\tilde{\mathbf v}}_i(x_i\mid\mathbf y)\bigr],\qquad\delta=\frac{\alpha}{1+\alpha\beta},$$
--   approach the agents in index order, and let each agent choose a utility-maximizing outcome given its own type and the allocation made so far. Then the resulting outcome profile $\mathbf x(\mathbf v)$ satisfies
--   $$\mathbb E_{\mathbf v}\bigl[\mathbf v(\mathbf x(\mathbf v))\bigr]\ \ge\ \frac1{1+\alpha\beta}\cdot\mathbb E_{\mathbf v}\bigl[\mathbf v(\mathrm{ALG}(\mathbf v))\bigr].$$
--
--   This is the paper's extension theorem: a pricing rule that is balanced for every full-information instance yields, after averaging over the instance and scaling by $\delta$, a posted-price mechanism that is $1/(1+\alpha\beta)$-competitive with $\mathrm{ALG}$ in the Bayesian setting. With $\mathrm{ALG}=\mathrm{OPT}$ it is a prophet inequality.
--
--   **Formalization Note** Agents are `Fin n`, 0-based; "the order they are indexed" is the order of `Fin n`. Valuation types are countable with the discrete σ-algebra (a disclosed restriction: the paper allows arbitrary distributions); valuations are bounded in $[0,1]$ as in §2. Prices are `ℝ≥0∞`-valued with `⊤` for $\infty$, and expected prices are Lebesgue integrals in $[0,\infty]$. The free null outcome, $p^{\tilde{\mathbf v}}_i(\varnothing\mid\mathbf y)=0$ for feasible $\mathbf y$, is a disclosed standing assumption satisfied by every pricing rule of the paper. The agents' behaviour is a choice rule `choice` that is assumed utility-maximizing (finite price, maximal $v_i(x_i)-\delta p_i(x_i\mid\mathbf y)$ among finitely priced outcomes) at every feasible partial allocation; the theorem says nothing when no maximizer exists. The constant $\delta=\alpha/(1+\alpha\beta)$ is fixed inside `postedPrice`.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 549, Theorem 3.2 (proof pp. 549–550)

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open MeasureTheory
open scoped ENNReal

namespace BalancedPrices.Extension

theorem theorem_3_2 {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (nul : Outcome X) (F : Set (Outcome X)) (hF : DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (ALG : (∀ i, V i) → Outcome X) (hALG : ∀ v, ALG v ∈ F)
    (pv : (∀ i, V i) → PriceRule X) (hrule : ∀ w, IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (hbal : ∃ Fam : Outcome X → Set (Outcome X), ExchFamily F Fam ∧
      ∀ w, Balanced nul α β F Fam (prof val w) (ALG w) (pv w))
    (choice : ∀ i, V i → Outcome X → X i)
    (hchoice : IsUtilMax F val (postedPrice α β μ pv) choice) :
    1 / (1 + α * β) * ∫ v, welfare (prof val v) (ALG v) ∂(Measure.pi μ) ≤
      ∫ v, welfare (prof val v) (run nul choice v) ∂(Measure.pi μ) := by sorry

end BalancedPrices.Extension
