-- Prove2me | Theorems.Thm_CongestionTaxes_display_14_line_5
-- name    : CongestionTaxes.display_14_line_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:17.364335+00:00
-- url     : https://prove2.me/theorems/e9ce349f-ab73-44de-afdb-57b0b5ec54b0
-- title:
--   Display (14), line 5, p.20 — loads of a profile are feasible, so $\sum_r p_r(\bar v_r)\le\sum_r p_r(|a|_r)$
-- statement:
--   Let $G$ be a congestion game and $a\in\mathcal A$ a profile. The point that puts weight $1$ on each agent's action $a_i$ is feasible for program (12), with loads $v_r=|a|_r$. Consequently every solution $\bigl((\bar y_i)_i,(\bar v_r)_r\bigr)$ of (12) satisfies
--
--   $$
--   \sum_{r\in\mathcal R}p_r(\bar v_r)\ \le\ \sum_{r\in\mathcal R}p_r(|a|_r).
--   $$
--
--   In the proof of Theorem 3 this is applied to an optimal allocation $a^{\mathrm{opt}}$, with $v^{\mathrm{opt}}_r=|a^{\mathrm{opt}}|_r$.
--
--   Differences from the source:
--
--   - generalization: $v^{\mathrm{opt}}_r=|a^{\mathrm{opt}}|_r$ for an optimal allocation → every profile $a\in\mathcal A$; reason: $a^{\mathrm{opt}}$ is a profile; the line uses only that its loads are feasible
--   - reading: sums over $r\in a$ in line 5 → sums over all $r\in\mathcal R$; reason: the comparison with (12)'s objective is over all resources; see the reading of lines 3–4
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (14), line 5, proof of Theorem 3, p.20

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_CongestionTaxes_poissonValue
import Definitions.Def_CongestionTaxes_IsFeasible
import Definitions.Def_CongestionTaxes_IsSolution

namespace CongestionTaxes

/-- Display (14), line 5 (Paccagnan, Gairing, arXiv:2105.07480v2, proof of Theorem 3, p.20,
"(v̄_r optimal solution of (12))"). For every profile `a ∈ 𝓐`, the point that puts weight `1` on
each agent's action `a_i` is feasible for (12), with loads `v_r = |a|_r`; hence every solution
`(ȳ, v̄)` of (12) satisfies `∑_r p_r(v̄_r) ≤ ∑_r p_r(|a|_r)`. In the proof `a` is `a^opt` and
`v^opt_r = |a^opt|_r`. -/
theorem display_14_line_5 {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E)
    (a : ι → Finset E) (ha : CongestionPoA.AsymSum.IsProfile G a) :
    IsFeasible G (fun i s => if s = a i then 1 else 0)
        (fun r => (CongestionPoA.AsymSum.load a r : ℝ)) ∧
      ∀ y v, IsSolution G y v →
        ∑ r, poissonValue (G.latency r) (v r) ≤
          ∑ r, poissonValue (G.latency r) (CongestionPoA.AsymSum.load a r : ℝ) := by sorry

end CongestionTaxes
