-- Prove2me | Theorems.Thm_BalancedPrices_Extension_eq_3_3
-- name    : BalancedPrices.Extension.eq_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:15.933512+00:00
-- url     : https://prove2.me/theorems/6ac0078e-b6e0-4fe6-9f03-88df0474b8b0
-- title:
--   (3.3), p. 550 — E_v[Σ_i u_i(v)] ≥ (1 − δβ)·E_{v,ṽ}[ṽ(OPT(ṽ, F_x(v)))]
-- statement:
--   Throughout, there are $n$ agents $N=\{1,\dots,n\}$; agent $i$ has an outcome space $X_i$ with a null outcome $\varnothing$, the feasible outcome profiles form a downward-closed set $\mathcal F\subseteq X=X_1\times\dots\times X_n$, and agent $i$'s type $v_i$ is drawn independently from a distribution $\mathcal D_i$ on a countable set $V_i$; a type $v_i$ values outcome $x_i$ at $v_i(x_i)\in[0,1]$. For each type profile $\tilde{\mathbf v}$ there is a full-information pricing rule $p^{\tilde{\mathbf v}}$ (prices in $[0,\infty]$, equal to $\infty$ for outcomes that cannot be feasibly added to the feasible partial allocation, and $0$ for the null outcome at feasible partial allocations). The posted prices are $\delta\,p_i(x_i\mid\mathbf y)$ with $p_i(x_i\mid\mathbf y)=\mathbb E_{\tilde{\mathbf v}\sim\mathcal D}[p^{\tilde{\mathbf v}}_i(x_i\mid\mathbf y)]$ and $\delta=\alpha/(1+\alpha\beta)$, where $\alpha>0$, $\beta\ge0$. Agents are approached in index order; each chooses, from its own type and the partial allocation so far, an outcome of finite price maximizing $v_i(x_i)-\delta p_i(x_i\mid\mathbf y)$. We write $\mathbf x(\mathbf v)$ for the resulting outcome profile, $\mathbf x_{[i-1]}(\mathbf v)$ for its restriction to the agents before $i$, and $u_i(\mathbf v)=v_i(x_i(\mathbf v))-\delta p_i(x_i(\mathbf v)\mid\mathbf x_{[i-1]}(\mathbf v))$ for agent $i$'s utility.
--
--   Suppose the collection $(p^{\mathbf v})_{\mathbf v}$ is $(\alpha,\beta)$-balanced with respect to $\mathrm{ALG}$ (an outcome rule with values in $\mathcal F$) and an exchange-compatible family $(\mathcal F_{\mathbf x})_{\mathbf x\in X}$. Then, with $\delta=\alpha/(1+\alpha\beta)$ and $\mathbf v,\tilde{\mathbf v}\sim\mathcal D$ independent,
--   $$\mathbb E_{\mathbf v}\Bigl[\sum_{i\in N}u_i(\mathbf v)\Bigr]\ \ge\ (1-\delta\beta)\cdot\mathbb E_{\mathbf v,\tilde{\mathbf v}}\bigl[\tilde{\mathbf v}(\mathrm{OPT}(\tilde{\mathbf v},\mathcal F_{\mathbf x(\mathbf v)}))\bigr].$$
--
--   This is the utility half of the proof of Theorem 3.2: (3.1) combined with (3.2).
--
--   **Formalization Note** Agents are `Fin n`, 0-based: the paper's agent $i$ is index $i-1$ and "the order they are indexed" is the order of `Fin n`. Valuation types are countable with the discrete σ-algebra (a disclosed restriction: the paper allows any distribution); this makes every function measurable and every bounded function integrable. Prices are `ℝ≥0∞`-valued with `⊤` for $\infty$. The null outcome being free ($p^{\mathbf v}_i(\varnothing\mid\mathbf y)=0$ for feasible $\mathbf y$) is a disclosed standing assumption, satisfied by every pricing rule in the paper and needed because the deviation $\mathrm{OPT}(\mathbf v',\mathcal F_{\mathbf x(\mathbf v)})$ of the proof does not exist when $\mathcal F_{\mathbf x(\mathbf v)}=\varnothing$. $\mathbf v(\mathrm{OPT}(\mathbf v,S))$ is the real supremum of the welfare over $S$, which is $0$ for $S=\varnothing$. Here $\tilde{\mathbf v}(\mathrm{OPT}(\tilde{\mathbf v},\cdot))$ is the exact supremum, so no selector appears. Both sides are real numbers.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 550, proof of Theorem 3.2, display (3.3)

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open MeasureTheory
open scoped ENNReal

namespace BalancedPrices.Extension

theorem eq_3_3 {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (nul : Outcome X) (F : Set (Outcome X)) (hF : DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (ALG : (∀ i, V i) → Outcome X) (hALG : ∀ v, ALG v ∈ F)
    (pv : (∀ i, V i) → PriceRule X) (hrule : ∀ w, IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (Fam : Outcome X → Set (Outcome X)) (hFam : ExchFamily F Fam)
    (hbal : ∀ w, Balanced nul α β F Fam (prof val w) (ALG w) (pv w))
    (choice : ∀ i, V i → Outcome X → X i)
    (hchoice : IsUtilMax F val (postedPrice α β μ pv) choice) :
    (1 - α / (1 + α * β) * β) *
        ∫ vv, optVal (prof val vv.2) (Fam (run nul choice vv.1)) ∂((Measure.pi μ).prod (Measure.pi μ)) ≤
      ∫ v, ∑ i, utility nul val (postedPrice α β μ pv) choice v i ∂(Measure.pi μ) := by sorry

end BalancedPrices.Extension
