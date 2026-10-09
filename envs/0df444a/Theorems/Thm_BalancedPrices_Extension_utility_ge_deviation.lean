-- Prove2me | Theorems.Thm_BalancedPrices_Extension_utility_ge_deviation
-- name    : BalancedPrices.Extension.utility_ge_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:37.748571+00:00
-- url     : https://prove2.me/theorems/f930a994-c30b-4c64-b075-552981e0d915
-- title:
--   Proof of Theorem 3.2, p. 549 — E_v[u_i(v)] ≥ E_{v,v′}[v′_i(x′_i(v, v′)) − δ·p_i(x′_i(v, v′) | x_[i−1](v))]
-- statement:
--   Throughout, there are $n$ agents $N=\{1,\dots,n\}$; agent $i$ has an outcome space $X_i$ with a null outcome $\varnothing$, the feasible outcome profiles form a downward-closed set $\mathcal F\subseteq X=X_1\times\dots\times X_n$, and agent $i$'s type $v_i$ is drawn independently from a distribution $\mathcal D_i$ on a countable set $V_i$; a type $v_i$ values outcome $x_i$ at $v_i(x_i)\in[0,1]$. For each type profile $\tilde{\mathbf v}$ there is a full-information pricing rule $p^{\tilde{\mathbf v}}$ (prices in $[0,\infty]$, equal to $\infty$ for outcomes that cannot be feasibly added to the feasible partial allocation, and $0$ for the null outcome at feasible partial allocations). The posted prices are $\delta\,p_i(x_i\mid\mathbf y)$ with $p_i(x_i\mid\mathbf y)=\mathbb E_{\tilde{\mathbf v}\sim\mathcal D}[p^{\tilde{\mathbf v}}_i(x_i\mid\mathbf y)]$ and $\delta=\alpha/(1+\alpha\beta)$, where $\alpha>0$, $\beta\ge0$. Agents are approached in index order; each chooses, from its own type and the partial allocation so far, an outcome of finite price maximizing $v_i(x_i)-\delta p_i(x_i\mid\mathbf y)$. We write $\mathbf x(\mathbf v)$ for the resulting outcome profile, $\mathbf x_{[i-1]}(\mathbf v)$ for its restriction to the agents before $i$, and $u_i(\mathbf v)=v_i(x_i(\mathbf v))-\delta p_i(x_i(\mathbf v)\mid\mathbf x_{[i-1]}(\mathbf v))$ for agent $i$'s utility.
--
--   Let $(\mathcal F_{\mathbf x})_{\mathbf x\in X}$ be an exchange-compatible family and let $\mathrm{dev}(\mathbf v',\mathbf x)\in\mathcal F_{\mathbf x}$ be any choice of a deviation profile whenever $\mathcal F_{\mathbf x}\ne\varnothing$. Draw $\mathbf v,\mathbf v'\sim\mathcal D$ independently and put $\mathbf x'(\mathbf v,\mathbf v')=\mathrm{dev}(\mathbf v',\mathbf x(\mathbf v))$. Then for every agent $i$
--   $$\mathbb E_{\mathbf v}[u_i(\mathbf v)]\ \ge\ \mathbb E_{\mathbf v,\mathbf v'}\Bigl[v'_i\bigl(x'_i(\mathbf v,\mathbf v')\bigr)-\delta\cdot p_i\bigl(x'_i(\mathbf v,\mathbf v')\mid\mathbf x_{[i-1]}(\mathbf v)\bigr)\Bigr],$$
--   where both terms inside the expectation are taken to be $0$ when $\mathcal F_{\mathbf x(\mathbf v)}=\varnothing$. The inequality is asserted in the form $\mathbb E[v'_i(x'_i)]\le\mathbb E[u_i]+\mathbb E[\delta p_i(x'_i\mid\mathbf x_{[i-1]})]$ in $[0,\infty]$.
--
--   This is the per-agent utility bound of the proof of Theorem 3.2: agent $i$ could have bought its part of a deviation that is feasible after the others' purchases.
--
--   **Formalization Note** Agents are `Fin n`, 0-based: the paper's agent $i$ is index $i-1$ and "the order they are indexed" is the order of `Fin n`. Valuation types are countable with the discrete σ-algebra (a disclosed restriction: the paper allows any distribution); this makes every function measurable and every bounded function integrable. Prices are `ℝ≥0∞`-valued with `⊤` for $\infty$. The null outcome being free ($p^{\mathbf v}_i(\varnothing\mid\mathbf y)=0$ for feasible $\mathbf y$) is a disclosed standing assumption, satisfied by every pricing rule in the paper and needed because the deviation $\mathrm{OPT}(\mathbf v',\mathcal F_{\mathbf x(\mathbf v)})$ of the proof does not exist when $\mathcal F_{\mathbf x(\mathbf v)}=\varnothing$. $\mathbf v(\mathrm{OPT}(\mathbf v,S))$ is the real supremum of the welfare over $S$, which is $0$ for $S=\varnothing$. The proof's deviation $\mathbf x'(\mathbf v,\mathbf v')=\mathrm{OPT}(\mathbf v',\mathcal F_{\mathbf x(\mathbf v)})$ is replaced by an arbitrary selector $\mathrm{dev}(\mathbf v',\mathbf x)\in\mathcal F_{\mathbf x}$ (whenever $\mathcal F_{\mathbf x}\neq\varnothing$), with the deviation's value and price counted as $0$ when $\mathcal F_{\mathbf x(\mathbf v)}=\varnothing$ (the paper's $\mathbf v'(\mathrm{OPT}(\mathbf v',\varnothing))=0$). This is a generalization (the supremum need not be attained), and the step is stated in $[0,\infty]$, $\mathrm{ofReal}(\mathbb E[\text{value}])\le\mathrm{ofReal}(\mathbb E[u])+\mathbb E[\text{price}]$, so that an infinite expected price makes it trivially true instead of being truncated.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 549, proof of Theorem 3.2 (Utility bound), the display before (3.1)

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open MeasureTheory
open scoped ENNReal

namespace BalancedPrices.Extension

open Classical in
theorem utility_ge_deviation {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (nul : Outcome X) (F : Set (Outcome X)) (hF : DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (pv : (∀ i, V i) → PriceRule X) (hrule : ∀ w, IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (Fam : Outcome X → Set (Outcome X)) (hFam : ExchFamily F Fam)
    (choice : ∀ i, V i → Outcome X → X i)
    (hchoice : IsUtilMax F val (postedPrice α β μ pv) choice)
    (dev : (∀ i, V i) → Outcome X → Outcome X)
    (hdev : ∀ w x, (Fam x).Nonempty → dev w x ∈ Fam x)
    (i : Fin n) :
    ENNReal.ofReal (∫ vv, (if (Fam (run nul choice vv.1)).Nonempty then
        val i (vv.2 i) (dev vv.2 (run nul choice vv.1) i) else 0) ∂((Measure.pi μ).prod (Measure.pi μ))) ≤
      ENNReal.ofReal (∫ v, utility nul val (postedPrice α β μ pv) choice v i ∂(Measure.pi μ)) +
        ∫⁻ vv, (if (Fam (run nul choice vv.1)).Nonempty then
          postedPrice α β μ pv i (dev vv.2 (run nul choice vv.1) i) (pre nul (run nul choice vv.1) i) else 0) ∂((Measure.pi μ).prod (Measure.pi μ)) := by sorry

end BalancedPrices.Extension
