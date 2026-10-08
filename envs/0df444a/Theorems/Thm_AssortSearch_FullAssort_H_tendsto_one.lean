-- Prove2me | Theorems.Thm_AssortSearch_FullAssort_H_tendsto_one
-- name    : AssortSearch.FullAssort.H_tendsto_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:03.683274+00:00
-- url     : https://prove2.me/theorems/7f7f3002-a219-4b29-85f8-d1965c7c6e0e
-- title:
--   Proof of Theorem 6, p. 18 — $H(\bar U(S),S)\to1$ as $b\to0$
-- statement:
--   Let $\mu > 0$, $v_1, \dots, v_n > 0$, $v_0 > 0$, and $S \subsetneq N$. As the search cost $b$ tends to $0$ from above,
--
--   $$H(\bar U_b(S), S) = \exp\Big(-\lambda(\bar U_b(S))\,\big(v_0 + \textstyle\sum_{j\in S} v_j\big)\Big) \longrightarrow 1,$$
--
--   and consequently every variant $i \in S$ has overlapping-assortment demand $q_i^{so}(S) = q_i^m(S)\,(1 - H(\bar U_b(S), S)) \to 0$.
--
--   The paper uses this in the proof of Theorem 6: for a sufficiently low $b$, $H$ is close enough to $1$ that the profit of any assortment other than the full one falls below the full-assortment profit.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 18 (PDF 20), proof of Theorem 6, (13)

import Mathlib
import Definitions.Def_AssortSearch_FullAssort_Model

namespace AssortSearch.FullAssort

open Filter Topology

/-- Proof of Theorem 6 (p. 18): for an assortment `S ⊊ N`, `H(Ū(S), S) → 1` as the search
cost `b → 0⁺`, so every variant's demand `q_i^so(S)` tends to `0`. -/
theorem H_tendsto_one {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (v0 : ℝ) (hv0 : 0 < v0) (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    Tendsto (fun b => AssortSearch.Cannibal.H μ (Ubar μ v S b) v v0 S) (𝓝[>] 0) (𝓝 1) ∧
      ∀ i ∈ S, Tendsto (fun b => demandSO μ v v0 b S i) (𝓝[>] 0) (𝓝 0) := by sorry

end AssortSearch.FullAssort
