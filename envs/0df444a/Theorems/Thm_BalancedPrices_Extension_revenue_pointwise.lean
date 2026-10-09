-- Prove2me | Theorems.Thm_BalancedPrices_Extension_revenue_pointwise
-- name    : BalancedPrices.Extension.revenue_pointwise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:16.829651+00:00
-- url     : https://prove2.me/theorems/1b74f157-eefd-4e49-bed4-480076edc56d
-- title:
--   Proof of Theorem 3.2, p. 550 — by (a), Σ_i δ·p_i(x_i | x_[i−1]) ≥ (δ/α)·E_ṽ[ṽ(ALG(ṽ)) − ṽ(OPT(ṽ, F_x))]
-- statement:
--   Throughout, there are $n$ agents $N=\{1,\dots,n\}$; agent $i$ has an outcome space $X_i$ with a null outcome $\varnothing$, the feasible outcome profiles form a downward-closed set $\mathcal F\subseteq X=X_1\times\dots\times X_n$, and agent $i$'s type $v_i$ is drawn independently from a distribution $\mathcal D_i$ on a countable set $V_i$; a type $v_i$ values outcome $x_i$ at $v_i(x_i)\in[0,1]$. For each type profile $\tilde{\mathbf v}$ there is a full-information pricing rule $p^{\tilde{\mathbf v}}$ (prices in $[0,\infty]$, equal to $\infty$ for outcomes that cannot be feasibly added to the feasible partial allocation, and $0$ for the null outcome at feasible partial allocations). The posted prices are $\delta\,p_i(x_i\mid\mathbf y)$ with $p_i(x_i\mid\mathbf y)=\mathbb E_{\tilde{\mathbf v}\sim\mathcal D}[p^{\tilde{\mathbf v}}_i(x_i\mid\mathbf y)]$ and $\delta=\alpha/(1+\alpha\beta)$, where $\alpha>0$, $\beta\ge0$. Agents are approached in index order; each chooses, from its own type and the partial allocation so far, an outcome of finite price maximizing $v_i(x_i)-\delta p_i(x_i\mid\mathbf y)$. We write $\mathbf x(\mathbf v)$ for the resulting outcome profile, $\mathbf x_{[i-1]}(\mathbf v)$ for its restriction to the agents before $i$, and $u_i(\mathbf v)=v_i(x_i(\mathbf v))-\delta p_i(x_i(\mathbf v)\mid\mathbf x_{[i-1]}(\mathbf v))$ for agent $i$'s utility.
--
--   Suppose the collection $(p^{\mathbf v})_{\mathbf v}$ is $(\alpha,\beta)$-balanced with respect to $\mathrm{ALG}$ and an exchange-compatible family $(\mathcal F_{\mathbf x})_{\mathbf x\in X}$. Then for every feasible outcome profile $\mathbf x\in\mathcal F$,
--   $$\sum_{i\in N}\delta\cdot p_i(x_i\mid\mathbf x_{[i-1]})\ \ge\ \frac\delta\alpha\cdot\mathbb E_{\tilde{\mathbf v}}\bigl[\tilde{\mathbf v}(\mathrm{ALG}(\tilde{\mathbf v}))-\tilde{\mathbf v}(\mathrm{OPT}(\tilde{\mathbf v},\mathcal F_{\mathbf x}))\bigr],$$
--   where $\delta=\alpha/(1+\alpha\beta)$ and $p_i=\mathbb E_{\tilde{\mathbf v}}[p^{\tilde{\mathbf v}}_i]$.
--
--   This is the revenue bound of the proof of Theorem 3.2, applied in the paper to $\mathbf x=\mathbf x(\mathbf v)$; it follows from property (a).
--
--   **Formalization Note** Agents are `Fin n`, 0-based: the paper's agent $i$ is index $i-1$ and "the order they are indexed" is the order of `Fin n`. Valuation types are countable with the discrete σ-algebra (a disclosed restriction: the paper allows any distribution); this makes every function measurable and every bounded function integrable. Prices are `ℝ≥0∞`-valued with `⊤` for $\infty$. The null outcome being free ($p^{\mathbf v}_i(\varnothing\mid\mathbf y)=0$ for feasible $\mathbf y$) is a disclosed standing assumption, satisfied by every pricing rule in the paper and needed because the deviation $\mathrm{OPT}(\mathbf v',\mathcal F_{\mathbf x(\mathbf v)})$ of the proof does not exist when $\mathcal F_{\mathbf x(\mathbf v)}=\varnothing$. $\mathbf v(\mathrm{OPT}(\mathbf v,S))$ is the real supremum of the welfare over $S$, which is $0$ for $S=\varnothing$. The statement holds for every $\mathbf x\in\mathcal F$, which contains the paper's case $\mathbf x=\mathbf x(\mathbf v)$. The price sum stays in $[0,\infty]$ and the real right side is passed through `ENNReal.ofReal` (a negative right side makes the bound trivial, as on the page).
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 550, proof of Theorem 3.2 (Revenue bound), the display before (3.4)

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open MeasureTheory
open scoped ENNReal

namespace BalancedPrices.Extension

theorem revenue_pointwise {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (nul : Outcome X) (F : Set (Outcome X)) (hF : DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (ALG : (∀ i, V i) → Outcome X) (hALG : ∀ v, ALG v ∈ F)
    (pv : (∀ i, V i) → PriceRule X) (hrule : ∀ w, IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (Fam : Outcome X → Set (Outcome X)) (hFam : ExchFamily F Fam)
    (hbal : ∀ w, Balanced nul α β F Fam (prof val w) (ALG w) (pv w)) :
    ∀ x ∈ F,
      ENNReal.ofReal (α / (1 + α * β) / α *
          ∫ w, (welfare (prof val w) (ALG w) - optVal (prof val w) (Fam x)) ∂(Measure.pi μ)) ≤
        ∑ i, postedPrice α β μ pv i (x i) (pre nul x i) := by sorry

end BalancedPrices.Extension
