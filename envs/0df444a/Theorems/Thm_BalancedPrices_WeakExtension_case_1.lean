-- Prove2me | Theorems.Thm_BalancedPrices_WeakExtension_case_1
-- name    : BalancedPrices.WeakExtension.case_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:05:17.793987+00:00
-- url     : https://prove2.me/theorems/6455168c-f155-41be-b07d-1d469febc56d
-- title:
--   Appendix A, Case 1, p. 560 — if β₂ ≥ 1/(2α), posting δp with δ = 1/(β₁ + 2β₂) earns 1/(α(2β₁ + 4β₂))·E_v[v(ALG(v))]
-- statement:
--   Assume the hypotheses of Theorem 3.5: the collection $(p^{v})_{v\in V}$ is weakly $(\alpha,\beta_1,\beta_2)$-balanced with respect to $\mathrm{ALG}$ and the indexing of the players, $\alpha>0$, $\beta_1,\beta_2\ge0$, $\beta_1+\beta_2\ge 1/\alpha$. Suppose moreover that
--   $$\beta_2 \ \ge\ \frac1{2\alpha}.$$
--   If the agents, approached in index order, maximize utility under the posted prices $\delta p$ with
--   $$\delta = \frac1{\beta_1+2\beta_2},\qquad p_i(x_i\mid y) = \mathbb E_{\tilde v}\bigl[p^{\tilde v}_i(x_i\mid y)\bigr],$$
--   then the expected welfare of the mechanism satisfies
--   $$\mathbb E_v\Bigl[\sum_i v_i(x_i(v))\Bigr] \ \ge\ \frac1{\alpha(2\beta_1+4\beta_2)}\,\mathbb E_{v}\bigl[v(\mathrm{ALG}(v))\bigr].$$
--
--   This is the first of the two cases into which the proof of Theorem 3.5 splits; in this case $\delta = 1/(\beta_1+\max\{2\beta_2,1/\alpha\})$ equals $1/(\beta_1+2\beta_2)$.
--
--   **Formalization Note.** Valuation spaces are countable with discrete σ-algebras (a disclosed restriction: every function is then measurable, and bounded ones integrable); valuations take values in $[0,1]$ (standing assumption of §2); the null outcome is free at feasible partial allocations (`hnull`, the paper's implicit convention, needed for $u_i\ge0$). The family $(\mathcal F_x)$ is chosen once for all $v$ and is exchange compatible for all $x\in X$. $\delta$ is written literally inside the posted prices. The hypothesis $\beta_1+\beta_2\ge1/\alpha$ is the theorem's and is kept, though this case does not need it. Agents are `Fin n`, 0-based.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 560, Appendix A (proof of Theorem 3.5), Combination, Case 1

import Mathlib
import Definitions.Def_BalancedPrices_WeakExtension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open MeasureTheory

namespace BalancedPrices.WeakExtension

theorem case_1
    {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (nul : BalancedPrices.Extension.Outcome X) (F : Set (BalancedPrices.Extension.Outcome X)) (hF : BalancedPrices.Extension.DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (α β₁ β₂ : ℝ) (hα : 0 < α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hsum : 1 / α ≤ β₁ + β₂)
    (hcase : 1 / (2 * α) ≤ β₂)
    (ALG : (∀ i, V i) → BalancedPrices.Extension.Outcome X) (hALG : ∀ v, ALG v ∈ F)
    (pv : (∀ i, V i) → BalancedPrices.Extension.PriceRule X)
    (hrule : ∀ w, BalancedPrices.Extension.IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (hwb : ∃ Fam : BalancedPrices.Extension.Outcome X → Set (BalancedPrices.Extension.Outcome X), BalancedPrices.Extension.ExchFamily F Fam ∧
      ∀ w, WeakBalanced nul α β₁ β₂ F Fam (BalancedPrices.Extension.prof val w) (ALG w) (pv w))
    (choice : ∀ i, V i → BalancedPrices.Extension.Outcome X → X i)
    (hchoice : BalancedPrices.Extension.IsUtilMax F val
      (fun i xi y => ENNReal.ofReal (1 / (β₁ + 2 * β₂)) * BalancedPrices.Extension.expPrice μ pv i xi y) choice) :
    1 / (α * (2 * β₁ + 4 * β₂)) * ∫ v, BalancedPrices.Extension.welfare (BalancedPrices.Extension.prof val v) (ALG v) ∂(Measure.pi μ) ≤
      ∫ v, BalancedPrices.Extension.welfare (BalancedPrices.Extension.prof val v) (BalancedPrices.Extension.run nul choice v) ∂(Measure.pi μ) := by sorry

end BalancedPrices.WeakExtension
