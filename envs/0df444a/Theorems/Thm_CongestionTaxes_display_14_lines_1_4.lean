-- Prove2me | Theorems.Thm_CongestionTaxes_display_14_lines_1_4
-- name    : CongestionTaxes.display_14_lines_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:46.725352+00:00
-- url     : https://prove2.me/theorems/5f7e4faf-a40c-46df-a836-285d462c54b4
-- title:
--   Display (14), lines 1–4, p.20 (corrected: sum over all resources) — the deviation sum dominates $\sum_r[c_r(|a|_r)-p_r(v_r)]$
-- statement:
--   Let $G$ be a congestion game whose resource costs satisfy Assumption 1 with $\rho_{\ell_r}<\infty$, let $\bigl((y_i)_i,(v_r)_r\bigr)$ be feasible for (12), and let $\bar C_i(a)=\sum_{r\in a_i}f_r(|a|_r,v_r)$ be the perceived cost under the taxes with parameters $v$. Then for every profile $a\in\mathcal A$,
--
--   $$
--   \sum_{i=1}^N\sum_{k=1}^{s_i}y_{i,k}\bigl[\bar C_i(a)-\bar C_i(a'_{i,k},a_{-i})\bigr]\ \ge\ \sum_{r\in\mathcal R}\bigl[c_r(|a|_r)-p_r(v_r)\bigr],
--   $$
--
--   where $c_r(x)=x\ell_r(x)$ and $a'_{i,k}$ ranges over the actions of agent $i$. In the paper this is the chain of lines 1–4 of (14), via Lemma 1(b), a change of the order of summation and Lemma 1(c).
--
--   Differences from the source:
--
--   - correction: $\sum_{r\in a}$ in lines 3–4 of (14) → $\sum_{r\in\mathcal R}$; reason: read literally line 3 is false (one agent, resources $r_1,r_2$, actions $\{r_1\},\{r_2\}$, $\ell\equiv1$, $\bar y=(1/2,1/2)$, $a=\{r_1\}$: line 2 is $0$, line 3 is $1/2$); unused resources contribute $-p_r(v_r)$ by Lemma 1(c) at $x=0$, and with all of $\mathcal R$ every line holds and the conclusion of (14) is unchanged
--   - generalization: $(\bar y,\bar v)$ an optimal solution of (12) → any feasible $(y,v)$; reason: lines 1–4 use only feasibility; a solution is feasible
--   - encoding: the four-line chain → its first member $\ge$ its last; reason: the chain's conclusion; each step is an equality or $\ge$
--   - generalization: Theorem 3's hypothesis $\sup_{\ell\in\mathcal L}\rho_\ell<\infty$ with every $\ell_r\in\mathcal L$ → $\rho_{\ell_r}<\infty$ for every $r$ (no uniform bound); reason: the chain uses only Lemma 1 for each $\ell_r$, which needs the series (10) to converge; Theorem 3's hypothesis implies it
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (14), lines 1–4, proof of Theorem 3, p.20

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_rho
import Definitions.Def_CongestionTaxes_poissonValue
import Definitions.Def_CongestionTaxes_taxedGame
import Definitions.Def_CongestionTaxes_IsFeasible

open scoped ENNReal

namespace CongestionTaxes

/-- Display (14), lines 1–4 (Paccagnan, Gairing, arXiv:2105.07480v2, proof of Theorem 3, p.20).
Let every resource cost satisfy Assumption 1 with `ρ_{ℓ_r} < ∞`, let `(y, v)` be feasible for (12),
and let `C̄_i` be the perceived cost with parameters `v`. Then for every profile `a ∈ 𝓐`,
`∑_i ∑_k y_{i,k} [C̄_i(a) − C̄_i(a'_{i,k}, a_{−i})] ≥ ∑_{r ∈ 𝓡} [c_r(|a|_r) − p_r(v_r)]`,
with `c_r(x) = x ℓ_r(x)` (by Lemma 1(b), a change of the order of summation, and Lemma 1(c)).

**Formalization Note** The right-hand side sums over all resources `𝓡`: a resource unused by `a`
contributes `−p_r(v_r)` through Lemma 1(c) at `x = 0`. The printed `∑_{r ∈ a}` makes line 3 false
(one agent, resources `r₁, r₂`, actions `{r₁}`, `{r₂}`, `ℓ ≡ 1`, `y = (1/2, 1/2)`, `a = {r₁}`: line 2
is `0`, line 3 is `1/2`). The actions `a'_{i,k}` are the elements of `G.strategies i`, and
`(a'_{i,k}, a_{−i})` is `Function.update a i s`. Only the conclusion of the four lines is stated. -/
theorem display_14_lines_1_4 {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E)
    (hℓ : ∀ r, Assumption1 (G.latency r)) (hρ : ∀ r, rho (G.latency r) < ⊤)
    (y : ι → Finset E → ℝ) (v : E → ℝ) (hf : IsFeasible G y v)
    (a : ι → Finset E) (ha : CongestionPoA.AsymSum.IsProfile G a) :
    ∑ r, ((CongestionPoA.AsymSum.load a r : ℝ) * G.latency r (CongestionPoA.AsymSum.load a r) -
        poissonValue (G.latency r) (v r)) ≤
      ∑ i, ∑ s ∈ G.strategies i, y i s *
        (CongestionPoA.AsymSum.cost (taxedGame G v) a i -
          CongestionPoA.AsymSum.cost (taxedGame G v) (Function.update a i s) i) := by sorry

end CongestionTaxes
