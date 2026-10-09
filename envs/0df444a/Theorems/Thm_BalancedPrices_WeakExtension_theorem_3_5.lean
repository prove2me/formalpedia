-- Prove2me | Theorems.Thm_BalancedPrices_WeakExtension_theorem_3_5
-- name    : BalancedPrices.WeakExtension.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:05:12.450999+00:00
-- url     : https://prove2.me/theorems/4bb0c988-2fae-4f90-aa41-94673c5860d7
-- title:
--   Theorem 3.5, p. 551 — posting δ·E_ṽ[p^ṽ] with δ = 1/(β₁ + max{2β₂, 1/α}) earns welfare ≥ 1/(α(2β₁ + 4β₂))·E_v[v(ALG(v))]
-- statement:
--   There are $n$ agents. Agent $i$ has an outcome space $X_i$ with a null outcome $\emptyset$, and the feasible outcome profiles form a downward-closed set $\mathcal F\subseteq X_1\times\cdots\times X_n$. Agent $i$'s valuation $v_i : X_i\to[0,1]$ is drawn independently from a known distribution $\mathcal D_i$; $\mathcal D = \prod_i\mathcal D_i$. An allocation rule $\mathrm{ALG}$ maps each valuation profile to a feasible outcome.
--
--   Suppose that the collection of pricing rules $(p^{v})_{v\in V}$ is **weakly $(\alpha,\beta_1,\beta_2)$-balanced** with respect to $\mathrm{ALG}$ and the indexing of the players $i=1,\dots,n$: there is one exchange-compatible family $(\mathcal F_x)_{x\in X}$ such that every $p^v$ satisfies properties (a) and (b) of Definition 3.4. Assume $\alpha>0$, $\beta_1,\beta_2\ge0$ and
--   $$\beta_1+\beta_2\ \ge\ \frac1\alpha.$$
--   Let
--   $$\delta = \frac{1}{\beta_1+\max\{2\beta_2,\,1/\alpha\}},\qquad p_i(x_i\mid y) = \mathbb E_{\tilde v}\bigl[p^{\tilde v}_i(x_i\mid y)\bigr].$$
--   Then the posted-price mechanism with pricing rule $\delta p$, approaching the players in the order they are indexed (each player buying a utility-maximizing outcome), generates expected welfare
--   $$\mathbb E_v\Bigl[\sum_i v_i(x_i(v))\Bigr] \ \ge\ \frac{1}{\alpha(2\beta_1+4\beta_2)}\,\mathbb E_v\bigl[v(\mathrm{ALG}(v))\bigr].$$
--
--   This extends Theorem 3.2 from $(\alpha,\beta)$-balanced to weakly balanced prices, whose property (b) may also charge a multiple of the benchmark welfare $v(\mathrm{ALG}(v))$. It is the extension theorem the paper uses for combinatorial auctions with bounded bundle size (Theorem 4.1) and MPH-$k$ valuations (Theorem 1.6), where the full-information prices are weakly $(1,1,d-1)$-balanced.
--
--   **Formalization Note.** Agents are `Fin n`, 0-based; "the order they are indexed" is the order of `Fin n`. Valuations are given by types $w\in V_i$ through $\mathrm{val}_i(w,\cdot)$, with values in $[0,1]$ (the standing assumption of §2). The type spaces are countable with discrete σ-algebras — a disclosed restriction of the page's general distributions, which makes every function measurable and every bounded one integrable. Prices are `ENNReal`-valued ($\infty = \top$) and must be $\infty$ for infeasible additions. The hypothesis `hnull` (the null outcome has price $0$ at feasible partial allocations) is the paper's implicit convention: every pricing rule in the paper satisfies it, and the proof uses its consequence $u_i(v)\ge0$. The family $(\mathcal F_x)$ is chosen once for all $v$ and is exchange compatible for all $x\in X$, as printed. Agents' behaviour is a choice rule that sees only the agent's own type and the partial allocation of earlier agents and maximizes utility at every feasible partial allocation. $\delta$ is written literally in the posted prices. $v(\mathrm{OPT}(v,S))$ is a supremum (0 on $\emptyset$).
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 551, Theorem 3.5 (proof: Appendix A, pp. 559–560)

import Mathlib
import Definitions.Def_BalancedPrices_WeakExtension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open MeasureTheory

namespace BalancedPrices.WeakExtension

theorem theorem_3_5
    {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (nul : BalancedPrices.Extension.Outcome X) (F : Set (BalancedPrices.Extension.Outcome X)) (hF : BalancedPrices.Extension.DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (α β₁ β₂ : ℝ) (hα : 0 < α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hsum : 1 / α ≤ β₁ + β₂)
    (ALG : (∀ i, V i) → BalancedPrices.Extension.Outcome X) (hALG : ∀ v, ALG v ∈ F)
    (pv : (∀ i, V i) → BalancedPrices.Extension.PriceRule X)
    (hrule : ∀ w, BalancedPrices.Extension.IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (hwb : ∃ Fam : BalancedPrices.Extension.Outcome X → Set (BalancedPrices.Extension.Outcome X), BalancedPrices.Extension.ExchFamily F Fam ∧
      ∀ w, WeakBalanced nul α β₁ β₂ F Fam (BalancedPrices.Extension.prof val w) (ALG w) (pv w))
    (choice : ∀ i, V i → BalancedPrices.Extension.Outcome X → X i)
    (hchoice : BalancedPrices.Extension.IsUtilMax F val
      (fun i xi y => ENNReal.ofReal (1 / (β₁ + max (2 * β₂) (1 / α))) * BalancedPrices.Extension.expPrice μ pv i xi y) choice) :
    1 / (α * (2 * β₁ + 4 * β₂)) * ∫ v, BalancedPrices.Extension.welfare (BalancedPrices.Extension.prof val v) (ALG v) ∂(Measure.pi μ) ≤
      ∫ v, BalancedPrices.Extension.welfare (BalancedPrices.Extension.prof val v) (BalancedPrices.Extension.run nul choice v) ∂(Measure.pi μ) := by sorry

end BalancedPrices.WeakExtension
