-- Prove2me | Theorems.Thm_BalancedPrices_WeakExtension_eq_A_3
-- name    : BalancedPrices.WeakExtension.eq_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:50.554228+00:00
-- url     : https://prove2.me/theorems/c6b5182c-f3b7-43bc-8b66-37ae14da810f
-- title:
--   (A.3), p. 559 — E_v[Σᵢ uᵢ(v)] ≥ (1 − δβ₁)·E_{v,ṽ}[ṽ(OPT(ṽ, F_x(v)))] − δβ₂·E_ṽ[ṽ(ALG(ṽ))]
-- statement:
--   Work in the setting of Theorem 3.5: weakly $(\alpha,\beta_1,\beta_2)$-balanced pricing rules $(p^{\tilde v})_{\tilde v}$ with respect to $\mathrm{ALG}$ and an exchange-compatible family $(\mathcal F_x)_{x\in X}$, with $\alpha>0$, $\beta_1,\beta_2\ge 0$; a scaling $\delta>0$; agents that maximize utility under the posted prices $\delta p$, $p_i(x_i\mid y) = \mathbb E_{\tilde v}[p^{\tilde v}_i(x_i\mid y)]$, approached in index order; $x(v)$ the resulting outcome. Then
--   $$\mathbb E_v\Bigl[\sum_i u_i(v)\Bigr] \ \ge\ (1-\delta\beta_1)\,\mathbb E_{v,\tilde v}\bigl[\tilde v(\mathrm{OPT}(\tilde v,\mathcal F_{x(v)}))\bigr] - \delta\beta_2\,\mathbb E_{\tilde v}\bigl[\tilde v(\mathrm{ALG}(\tilde v))\bigr].$$
--
--   This lower bound on the agents' total expected utility combines the utility bound (A.1), with the ghost sample renamed $\tilde v$, and the price bound (A.2). It is the utility half of the proof of Theorem 3.5.
--
--   **Formalization Note.** $\tilde v(\mathrm{OPT}(\tilde v,S))$ is the supremum of welfare over $S$ (0 for $S=\emptyset$), not an attained maximum. The statement is in $\mathbb R$; all quantities are bounded. The page writes the last term as $\mathbb E_{v,\tilde v}$; it does not depend on $v$. $\delta>0$ is arbitrary here (Theorem 3.5 fixes it in each case). `hnull`: the null outcome is free at feasible partial allocations (standing convention, see `utility_nonneg`). Agents are `Fin n`, 0-based.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 559, Appendix A (proof of Theorem 3.5), display (A.3)

import Mathlib
import Definitions.Def_BalancedPrices_WeakExtension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open MeasureTheory

namespace BalancedPrices.WeakExtension

theorem eq_A_3
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
    (1 - δ * β₁) * (∫ v, ∫ w, BalancedPrices.Extension.optVal (BalancedPrices.Extension.prof val w) (Fam (BalancedPrices.Extension.run nul choice v))
        ∂(Measure.pi μ) ∂(Measure.pi μ)) -
      δ * β₂ * ∫ w, BalancedPrices.Extension.welfare (BalancedPrices.Extension.prof val w) (ALG w) ∂(Measure.pi μ) ≤
    ∫ v, ∑ i, BalancedPrices.Extension.utility nul val (fun i xi y => ENNReal.ofReal δ * BalancedPrices.Extension.expPrice μ pv i xi y)
      choice v i ∂(Measure.pi μ) := by sorry

end BalancedPrices.WeakExtension
