-- Prove2me | Theorems.Thm_BalancedPrices_WeakExtension_eq_A_4
-- name    : BalancedPrices.WeakExtension.eq_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:46.044986+00:00
-- url     : https://prove2.me/theorems/df1accf8-a452-4dc6-b603-f53a8d427328
-- title:
--   (A.4), p. 559 — revenue bound: E_v[Σᵢ δ·pᵢ(xᵢ(v) | x_[i−1](v))] ≥ (δ/α)·E[ṽ(ALG(ṽ))] − (δ/α)·E_{ṽ,v}[ṽ(OPT(ṽ, F_x(v)))]
-- statement:
--   Work in the setting of Theorem 3.5: weakly $(\alpha,\beta_1,\beta_2)$-balanced pricing rules $(p^{\tilde v})_{\tilde v}$ with respect to $\mathrm{ALG}$ and an exchange-compatible family $(\mathcal F_x)_{x\in X}$, $\alpha>0$, $\beta_1,\beta_2\ge0$; a scaling $\delta>0$; utility-maximizing agents under the posted prices $\delta p$, $p_i(x_i\mid y)=\mathbb E_{\tilde v}[p^{\tilde v}_i(x_i\mid y)]$; $x(v)$ the outcome of the mechanism. Then the expected revenue satisfies
--   $$\mathbb E_v\Bigl[\sum_i \delta\, p_i\bigl(x_i(v)\bigm| x_{[i-1]}(v)\bigr)\Bigr] \ \ge\ \frac\delta\alpha\,\mathbb E_{\tilde v}\bigl[\tilde v(\mathrm{ALG}(\tilde v))\bigr] - \frac\delta\alpha\,\mathbb E_{\tilde v,v}\bigl[\tilde v(\mathrm{OPT}(\tilde v,\mathcal F_{x(v)}))\bigr].$$
--
--   This is property (a) of Definition 3.4, applied to the feasible outcome $x(v)$ and averaged over $\tilde v$ and $v$; it is the revenue half of the proof of Theorem 3.5.
--
--   **Formalization Note.** The revenue is the sum of the real values of the prices paid along the run. These prices are finite: agents only buy at finite prices at feasible partial allocations, and the run stays feasible (prices are $\infty$ off $\mathcal F$ and $\delta>0$), so the conversion `toReal` introduces no junk value; the solver has to establish this finiteness from the hypotheses. $\delta>0$ is arbitrary here. `hnull`: standing convention, see `utility_nonneg`. Agents are `Fin n`, 0-based.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 559, Appendix A (proof of Theorem 3.5), Revenue bound, display (A.4)

import Mathlib
import Definitions.Def_BalancedPrices_WeakExtension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open MeasureTheory

namespace BalancedPrices.WeakExtension

theorem eq_A_4
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
    (hchoice : BalancedPrices.Extension.IsUtilMax F val (fun i xi y => ENNReal.ofReal δ * BalancedPrices.Extension.expPrice μ pv i xi y) choice) :
    δ / α * (∫ w, BalancedPrices.Extension.welfare (BalancedPrices.Extension.prof val w) (ALG w) ∂(Measure.pi μ)) -
      δ / α * (∫ v, ∫ w, BalancedPrices.Extension.optVal (BalancedPrices.Extension.prof val w) (Fam (BalancedPrices.Extension.run nul choice v))
        ∂(Measure.pi μ) ∂(Measure.pi μ)) ≤
    ∫ v, ∑ i, (ENNReal.ofReal δ * BalancedPrices.Extension.expPrice μ pv i (BalancedPrices.Extension.run nul choice v i)
      (BalancedPrices.Extension.pre nul (BalancedPrices.Extension.run nul choice v) i)).toReal ∂(Measure.pi μ) := by sorry

end BalancedPrices.WeakExtension
