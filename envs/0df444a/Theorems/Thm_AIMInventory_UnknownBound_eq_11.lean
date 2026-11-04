-- Prove2me | Theorems.Thm_AIMInventory_UnknownBound_eq_11
-- name    : AIMInventory.UnknownBound.eq_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:02.574722+00:00
-- url     : https://prove2.me/theorems/7d7e6041-8b45-4617-b383-c40c27a59c45
-- title:
--   Proof of Theorem 7, Eq. (11): cost after the projection reaches the newsvendor level
-- statement:
--   For a horizon $T\ge1$, sum over the rounds $1\le t\le T$ satisfying $t\ge(y^{NV})^{2/\delta}$. The modified AIM target has expected cumulative newsvendor cost gap bounded by
--
--   $$\mathbb E\!\left[\sum_{\substack{1\le t\le T\\t\ge(y^{NV})^{2/\delta}}}\bigl(Q(\hat y^\delta_t)-Q(y^{NV})\bigr)\right]\le\max\{b,h\}\,T^{1/2+\delta}+\max\{b,h\}\,T^{1/2}.$$
--
--   This is the late-round contribution to the total regret guarantee, when $y^{NV}$ lies within the growing projection intervals.
--
--   **Formalization Note** The finite horizon restriction implicit in the page is explicit. If $y^{NV}=0$, the sum starts at round one, even though the paper's ceiling threshold is zero. The initial target lies in $[0,1]$.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 12, proof of Theorem 7, Eq. (11); https://doi.org/10.1287/moor.1080.0355

import Definitions.Def_AIMInventory_UnknownBound_AIM

open MeasureTheory

namespace AIMInventory.UnknownBound

/-- Equation (11) in the proof of Theorem 7, over the rounds whose
projection interval contains the newsvendor quantity. -/
theorem eq_11 (P : CappedBaseStock.DemandLaw) (δ b h y₁ : ℝ) (T : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 < b) (hh : 0 < h)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (hT : 1 ≤ T) :
    (∫ d : CappedBaseStock.DemandPath,
        (∑ t ∈ lateRounds δ (newsvendor P h b) T,
          (cost P h b (modAimTarget δ b h y₁ d t) - cost P h b (newsvendor P h b)))
          ∂CappedBaseStock.demandPathLaw P) ≤
      max b h * Real.rpow (T : ℝ) ((1 / 2 : ℝ) + δ) +
        max b h * Real.rpow (T : ℝ) (1 / 2 : ℝ) := by sorry

end AIMInventory.UnknownBound
