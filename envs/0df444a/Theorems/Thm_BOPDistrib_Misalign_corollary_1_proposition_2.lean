-- Prove2me | Theorems.Thm_BOPDistrib_Misalign_corollary_1_proposition_2
-- name    : BOPDistrib.Misalign.corollary_1_proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:35.033604+00:00
-- url     : https://prove2.me/theorems/a66135c1-8788-42ed-b046-7d97d3995738
-- title:
--   Corollary 1 + Proposition 2, pp. 16–17, 47 (PDF 17–18, 48) — F is profit-optimal iff m ≤ m^F, α ≥ a_F(m); F has least consumer surplus iff α ≥ a^cs_F(m); MR optimal and best for consumers at high ATP
-- statement:
--   Fix the parameters and an ATP $m$ satisfying the standing assumptions of the model: $w\le m<v_h$, $0\le m$, $0<\beta<1$, $0\le\gamma<1$, $0<\theta_0<1$, $c_\theta>0$, and the strict homogeneous Assumption 1, $0<b<c_\theta(1-\theta_0)+\beta(v_h-m)$. Then there is a threshold $a^{cs}_F(m)\in[0,\infty]$ with the following properties.
--
--   **Proposition 2.** For every risk aversion $\alpha>0$:
--   1. strategy MR induces the largest consumer surplus among F, M, FR, MR, and $CS^{MR}\ge CS^M\ge CS^F$;
--   2. strategy F induces the smallest consumer surplus if and only if $\alpha\ge a^{cs}_F(m)$.
--
--   **Corollary 1 and the combined claim.** If moreover $w\le\bar w=\beta v_h+(1-\beta)y$ and $c_\theta\le\bar c_\theta=(1-\beta)(w-y)$, then:
--   1. $m^F\le m^{MR}\le v_h$ and $m^F\le\bar m^{MR}\le v_h$;
--   2. there is a threshold $a_F(m)\in[0,\infty]$ such that, for every $\alpha>0$,
--   $$\Pi^F\ge\max(\Pi^M,\Pi^{FR},\Pi^{MR})\iff m\le m^F\ \text{and}\ \alpha\ge a_F(m),$$
--   and
--   $$\Pi^F\ge\max(\Pi^M,\Pi^{FR},\Pi^{MR})\ \text{and}\ CS^F\le\min(CS^{MR},CS^M,CS^{FR})\iff m\le m^F\ \text{and}\ \alpha\ge\max\big(a_F(m),a^{cs}_F(m)\big);$$
--   3. if $m\ge\max(m^{MR},\bar m^{MR})$, then MR is profit-optimal for every $\alpha>0$.
--
--   In words: at low ability to pay and high risk aversion (the BOP), the profit-maximizing allocation subsidizes customers without returns, and exactly then it induces the lowest consumer surplus once risk aversion also exceeds $a^{cs}_F(m)$. At high ability to pay, the profit-maximizing allocation (education with returns) is also the one that maximizes consumer surplus.
--
--   **Formalization Note** The ATP thresholds are pinned to the proof's formulas: $m^F=(c_\theta/\beta+w-\gamma v_h)/(1-\gamma)$, and $m^{MR}$, $\bar m^{MR}$ as on p. 44. The page only asserts that they exist. The risk-aversion thresholds $a_F(m)$ and $a^{cs}_F(m)$ are existential in $[0,\infty]$, with $\infty$ meaning "never", and fixed before $\alpha$. The hypotheses $w\le\bar w$ and $c_\theta\le\bar c_\theta$ apply only to Corollary 1, as on the page; Proposition 2 is stated without them. Added relative to the page: $\alpha>0$ in place of $\alpha\ge0$ (the refund divides by $\alpha$); $\gamma<1$ ($m^F$ divides by $1-\gamma$; the paper treats only $\gamma\le1$); $0<\theta_0<1$ and $c_\theta>0$ (divisions in $x^F$, $\theta^M$); $0\le m$ (ATP is nonnegative and the refund cannot exceed the price); and $m<v_h$, $b>0$ with Assumption 1 strict, because at the boundary the F and M allocations coincide and "F optimal only if $m\le m^F$" fails. The pricing stage is Proposition B.1's outcome.
-- source:
--   Calmon, Jue-Rajasingh, Romero & Stenson, Operational strategies for distributing durable goods in the base of the pyramid, accepted manuscript (M&SOM 24(4), 2022; TSpace, SSRN 2882402), pp. 16–17 (PDF 17–18), Corollary 1 and Proposition 2; p. 47 (PDF 48), proof of Proposition 2

import Mathlib
import Definitions.Def_BOPDistrib_Misalign_Model

namespace BOPDistrib.Misalign

/-- Corollary 1 (bullets 1–2, p. 16) and Proposition 2 (p. 17), combined as in the proof of
Proposition 2 (p. 47). For the homogeneous-ATP model at ATP `m`, there is a threshold
`a^cs_F(m) ∈ [0, ∞]` such that:
* (Proposition 2) for every `α > 0`, MR induces the largest consumer surplus and
  `CS^MR ≥ CS^M ≥ CS^F`, and F induces the smallest consumer surplus iff `α ≥ a^cs_F(m)`;
* (Corollary 1, if `w ≤ w̄` and `cθ ≤ c̄θ`) `m^F ≤ m^MR, m̄^MR ≤ v_h`; there is a threshold
  `a_F(m) ∈ [0, ∞]` such that F is profit-optimal iff `m ≤ m^F` and `α ≥ a_F(m)`, and F is both
  profit-optimal and of smallest consumer surplus iff `m ≤ m^F` and `α ≥ max(a_F(m), a^cs_F(m))`;
  and MR is profit-optimal for every `α > 0` whenever `m ≥ max(m^MR, m̄^MR)`. -/
theorem corollary_1_proposition_2 (P : Params) (m : ℝ) (hS : Standing P m) :
    ∃ acs : ENNReal,
      (∀ α : ℝ, 0 < α → MRMaxCS P m α ∧ CSF P m ≤ CSM P m ∧ CSM P m ≤ CSMR P m α) ∧
      (∀ α : ℝ, 0 < α → (FMinCS P m α ↔ acs ≤ ENNReal.ofReal α)) ∧
      (P.w ≤ wbar P → P.cθ ≤ cθbar P →
        (mF P ≤ mMR P ∧ mF P ≤ mMRbar P ∧ mMR P ≤ P.vh ∧ mMRbar P ≤ P.vh) ∧
        (∃ aF : ENNReal, ∀ α : ℝ, 0 < α →
          (FOpt P m α ↔ m ≤ mF P ∧ aF ≤ ENNReal.ofReal α) ∧
          (FOpt P m α ∧ FMinCS P m α ↔ m ≤ mF P ∧ max aF acs ≤ ENNReal.ofReal α)) ∧
        (max (mMR P) (mMRbar P) ≤ m → ∀ α : ℝ, 0 < α → MROpt P m α)) := by sorry

end BOPDistrib.Misalign
