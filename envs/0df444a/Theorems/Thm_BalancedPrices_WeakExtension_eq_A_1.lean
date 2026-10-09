-- Prove2me | Theorems.Thm_BalancedPrices_WeakExtension_eq_A_1
-- name    : BalancedPrices.WeakExtension.eq_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:48.385124+00:00
-- url     : https://prove2.me/theorems/a84361f7-82b2-4613-8e48-28ac2f507a03
-- title:
--   (A.1), p. 559 — utility bound: E_v[Σᵢ uᵢ(v)] ≥ E_{v,v′}[v′(x′(v, v′))] − E_{v,v′}[Σᵢ δ·pᵢ(x′ᵢ(v, v′) | x_[i−1](v))]
-- statement:
--   Work in the setting of Theorem 3.5: $n$ agents, null outcomes, a downward-closed feasible set $\mathcal F$ containing the null profile, countable type spaces with independent distributions, valuations in $[0,1]$, pricing rules $(p^{\tilde v})_{\tilde v}$ that charge $\infty$ for infeasible additions and $0$ for the null outcome at feasible partial allocations, an exchange-compatible family $(\mathcal F_x)_{x\in X}$, a scaling $\delta>0$, and utility-maximizing agents under the posted prices $\delta p$, $p_i(x_i\mid y) = \mathbb E_{\tilde v}[p^{\tilde v}_i(x_i\mid y)]$. Write $x(v)$ for the outcome of the mechanism on $v$.
--
--   Let $x'(w, x)$ be **any** selector with $x'(w,x)\in\mathcal F_x$ whenever $\mathcal F_x\neq\emptyset$, and put $x'(v,v') := x'(v', x(v))$, the deviation evaluated with a ghost sample $v'\sim\mathcal D$ independent of $v$. With the convention that the deviation contributes nothing when $\mathcal F_{x(v)}=\emptyset$,
--   $$\mathbb E_v\Bigl[\sum_{i} u_i(v)\Bigr] \ \ge\ \mathbb E_{v,v'}\bigl[v'(x'(v,v'))\bigr] - \mathbb E_{v,v'}\Bigl[\sum_{i}\delta\, p_i\bigl(x'_i(v,v')\bigm| x_{[i-1]}(v)\bigr)\Bigr].$$
--
--   This is the utility bound of the proof of Theorem 3.5: each agent could have bought its part of the deviation at the posted price, and the bound aggregates these options over the agents.
--
--   **Formalization Note.** The page prints "$=$" in (A.1); only "$\ge$" holds (agents maximize utility and the deviation is one option among many), as in the corresponding display of the proof of Theorem 3.2, so the inequality is stated. The page takes $x'(v,v') = \mathrm{OPT}(v',\mathcal F_{x(v)})$, a maximizer; the statement holds for every selector into $\mathcal F_{x(v)}$, which includes the maximizer when it exists and avoids assuming that the supremum is attained. Because the price term can be $\infty$, the inequality is stated rearranged in `ENNReal`, $\mathrm{ofReal}(\mathbb E[v'(x')]) \le \mathrm{ofReal}(\mathbb E[\sum_i u_i]) + \mathbb E[\sum_i \delta p_i]$; an infinite price term makes it trivially true rather than producing a junk real value. Inner expectations of real quantities are Bochner integrals of bounded functions on countable discrete spaces, hence well defined. `hnull`, `hnF`: see `utility_nonneg`. Agents are `Fin n`, 0-based.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 559, Appendix A (proof of Theorem 3.5), Utility bound, display (A.1)

import Mathlib
import Definitions.Def_BalancedPrices_WeakExtension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open MeasureTheory

namespace BalancedPrices.WeakExtension

open Classical in
theorem eq_A_1
    {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (nul : BalancedPrices.Extension.Outcome X) (F : Set (BalancedPrices.Extension.Outcome X)) (hF : BalancedPrices.Extension.DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (hnF : nul ∈ F)
    (pv : (∀ i, V i) → BalancedPrices.Extension.PriceRule X)
    (hrule : ∀ w, BalancedPrices.Extension.IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (Fam : BalancedPrices.Extension.Outcome X → Set (BalancedPrices.Extension.Outcome X)) (hFam : BalancedPrices.Extension.ExchFamily F Fam)
    (δ : ℝ) (hδ : 0 < δ)
    (choice : ∀ i, V i → BalancedPrices.Extension.Outcome X → X i)
    (hchoice : BalancedPrices.Extension.IsUtilMax F val (fun i xi y => ENNReal.ofReal δ * BalancedPrices.Extension.expPrice μ pv i xi y) choice)
    (dev : (∀ i, V i) → BalancedPrices.Extension.Outcome X → BalancedPrices.Extension.Outcome X)
    (hdev : ∀ w x, (Fam x).Nonempty → dev w x ∈ Fam x) :
    ENNReal.ofReal (∫ v, ∫ v', (if (Fam (BalancedPrices.Extension.run nul choice v)).Nonempty then
        BalancedPrices.Extension.welfare (BalancedPrices.Extension.prof val v') (dev v' (BalancedPrices.Extension.run nul choice v)) else 0) ∂(Measure.pi μ) ∂(Measure.pi μ)) ≤
      ENNReal.ofReal (∫ v, ∑ i, BalancedPrices.Extension.utility nul val
          (fun i xi y => ENNReal.ofReal δ * BalancedPrices.Extension.expPrice μ pv i xi y) choice v i ∂(Measure.pi μ)) +
        ∫⁻ v, ∫⁻ v', (if (Fam (BalancedPrices.Extension.run nul choice v)).Nonempty then
          ∑ i, ENNReal.ofReal δ * BalancedPrices.Extension.expPrice μ pv i (dev v' (BalancedPrices.Extension.run nul choice v) i)
            (BalancedPrices.Extension.pre nul (BalancedPrices.Extension.run nul choice v) i) else 0) ∂(Measure.pi μ) ∂(Measure.pi μ) := by sorry

end BalancedPrices.WeakExtension
