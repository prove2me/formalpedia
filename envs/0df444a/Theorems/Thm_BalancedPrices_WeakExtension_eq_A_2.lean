-- Prove2me | Theorems.Thm_BalancedPrices_WeakExtension_eq_A_2
-- name    : BalancedPrices.WeakExtension.eq_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:46.783082+00:00
-- url     : https://prove2.me/theorems/12d71148-6525-4d96-a305-1dd6269e3d51
-- title:
--   (A.2), p. 559 — by property (b), the deviation's expected price is at most δβ₁·E[ṽ(OPT(ṽ, F_x(v)))] + δβ₂·E[ṽ(ALG(ṽ))]
-- statement:
--   Work in the setting of Theorem 3.5, with an exchange-compatible family $(\mathcal F_x)_{x\in X}$ such that for every $\tilde v$ the pricing rule $p^{\tilde v}$ is weakly $(\alpha,\beta_1,\beta_2)$-balanced with respect to $\mathrm{ALG}$ and $(\mathcal F_x)$, a scaling $\delta>0$, utility-maximizing agents under the posted prices $\delta p$ with $p_i(x_i\mid y)=\mathbb E_{\tilde v}[p^{\tilde v}_i(x_i\mid y)]$, and a selector $x'(w,x)\in\mathcal F_x$ (whenever $\mathcal F_x\ne\emptyset$) as in (A.1). Then:
--
--   1. **Pointwise bound.** For every feasible $x\in\mathcal F$ and every $x'\in\mathcal F_x$,
--   $$\sum_i \delta\, p_i\bigl(x'_i\bigm| x_{[i-1]}\bigr) \ \le\ \delta\beta_1\,\mathbb E_{\tilde v}\bigl[\tilde v(\mathrm{OPT}(\tilde v,\mathcal F_x))\bigr] + \delta\beta_2\,\mathbb E_{\tilde v}\bigl[\tilde v(\mathrm{ALG}(\tilde v))\bigr].$$
--   2. **(A.2).** Taking $x = x(v)$ and $x' = x'(v,v')$ and the expectation over $v, v'$,
--   $$\mathbb E_{v,v'}\Bigl[\sum_i \delta\, p_i\bigl(x'_i(v,v')\bigm| x_{[i-1]}(v)\bigr)\Bigr] \ \le\ \delta\beta_1\,\mathbb E_{v,\tilde v}\bigl[\tilde v(\mathrm{OPT}(\tilde v,\mathcal F_{x(v)}))\bigr] + \delta\beta_2\,\mathbb E_{\tilde v}\bigl[\tilde v(\mathrm{ALG}(\tilde v))\bigr].$$
--
--   The bound is property (b) of Definition 3.4 averaged over the full-information profile $\tilde v$; it controls the cost of the deviation used in (A.1).
--
--   **Formalization Note.** Prices and their expectations are in `ENNReal`; the right sides are passed through `ENNReal.ofReal`. When $\mathcal F_{x(v)} = \emptyset$ the deviation term is $0$ (convention of (A.1)). The page writes the second term as $\mathbb E_{v,\tilde v}[\tilde v(\mathrm{ALG}(\tilde v))]$; it does not depend on $v$, so it is stated as $\mathbb E_{\tilde v}$. The second statement needs $x(v)\in\mathcal F$, which follows from the hypotheses (prices are $\infty$ off $\mathcal F$, $\delta>0$, agents buy at finite prices). $\delta>0$ is arbitrary; `hnull`: see `utility_nonneg`. Agents are `Fin n`, 0-based.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 559, Appendix A (proof of Theorem 3.5), the pointwise display after (A.1) and display (A.2)

import Mathlib
import Definitions.Def_BalancedPrices_WeakExtension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open MeasureTheory

namespace BalancedPrices.WeakExtension

open Classical in
theorem eq_A_2
    {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (nul : BalancedPrices.Extension.Outcome X) (F : Set (BalancedPrices.Extension.Outcome X)) (hF : BalancedPrices.Extension.DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (α β₁ β₂ : ℝ) (hα : 0 < α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (ALG : (∀ i, V i) → BalancedPrices.Extension.Outcome X) (hALG : ∀ v, ALG v ∈ F)
    (pv : (∀ i, V i) → BalancedPrices.Extension.PriceRule X)
    (hrule : ∀ w, BalancedPrices.Extension.IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (Fam : BalancedPrices.Extension.Outcome X → Set (BalancedPrices.Extension.Outcome X)) (hFam : BalancedPrices.Extension.ExchFamily F Fam)
    (hwb : ∀ w, WeakBalanced nul α β₁ β₂ F Fam (BalancedPrices.Extension.prof val w) (ALG w) (pv w))
    (δ : ℝ) (hδ : 0 < δ)
    (choice : ∀ i, V i → BalancedPrices.Extension.Outcome X → X i)
    (hchoice : BalancedPrices.Extension.IsUtilMax F val (fun i xi y => ENNReal.ofReal δ * BalancedPrices.Extension.expPrice μ pv i xi y) choice)
    (dev : (∀ i, V i) → BalancedPrices.Extension.Outcome X → BalancedPrices.Extension.Outcome X)
    (hdev : ∀ w x, (Fam x).Nonempty → dev w x ∈ Fam x) :
    (∀ x ∈ F, ∀ x' ∈ Fam x,
      ∑ i, ENNReal.ofReal δ * BalancedPrices.Extension.expPrice μ pv i (x' i) (BalancedPrices.Extension.pre nul x i) ≤
        ENNReal.ofReal (δ * β₁ * ∫ w, BalancedPrices.Extension.optVal (BalancedPrices.Extension.prof val w) (Fam x) ∂(Measure.pi μ) +
          δ * β₂ * ∫ w, BalancedPrices.Extension.welfare (BalancedPrices.Extension.prof val w) (ALG w) ∂(Measure.pi μ))) ∧
    ∫⁻ v, ∫⁻ v', (if (Fam (BalancedPrices.Extension.run nul choice v)).Nonempty then
        ∑ i, ENNReal.ofReal δ * BalancedPrices.Extension.expPrice μ pv i (dev v' (BalancedPrices.Extension.run nul choice v) i)
          (BalancedPrices.Extension.pre nul (BalancedPrices.Extension.run nul choice v) i) else 0) ∂(Measure.pi μ) ∂(Measure.pi μ) ≤
      ENNReal.ofReal (δ * β₁ * ∫ v, ∫ w, BalancedPrices.Extension.optVal (BalancedPrices.Extension.prof val w) (Fam (BalancedPrices.Extension.run nul choice v))
          ∂(Measure.pi μ) ∂(Measure.pi μ) +
        δ * β₂ * ∫ w, BalancedPrices.Extension.welfare (BalancedPrices.Extension.prof val w) (ALG w) ∂(Measure.pi μ)) := by sorry

end BalancedPrices.WeakExtension
