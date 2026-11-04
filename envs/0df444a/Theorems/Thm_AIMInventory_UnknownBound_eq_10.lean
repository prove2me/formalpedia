-- Prove2me | Theorems.Thm_AIMInventory_UnknownBound_eq_10
-- name    : AIMInventory.UnknownBound.eq_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:51.127318+00:00
-- url     : https://prove2.me/theorems/378411fd-e760-496b-bf8f-dba6f8d9e153
-- title:
--   Proof of Theorem 7, Eq. (10): cost before the projection reaches the newsvendor level
-- statement:
--   For a horizon $T\ge1$, sum over the rounds $1\le t\le T$ satisfying $t<(y^{NV})^{2/\delta}$. The modified AIM target has expected cumulative newsvendor cost gap bounded by
--
--   $$\mathbb E\!\left[\sum_{\substack{1\le t\le T\\t<(y^{NV})^{2/\delta}}}\bigl(Q(\hat y^\delta_t)-Q(y^{NV})\bigr)\right]\le\max\{b,h\}\,(y^{NV})^{1+2/\delta}.$$
--
--   This is the finite contribution from the early rounds, before the projection interval grows large enough to contain the newsvendor level.
--
--   **Formalization Note** The page suppresses the horizon restriction in the displayed sum; the theorem states it explicitly. The initial target lies in $[0,1]$. At $y^{NV}=0$ the index set is empty and both sides are zero.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 12, proof of Theorem 7, Eq. (10); https://doi.org/10.1287/moor.1080.0355

import Definitions.Def_AIMInventory_UnknownBound_AIM

open MeasureTheory

namespace AIMInventory.UnknownBound

/-- Equation (10) in the proof of Theorem 7, over the rounds before the
expanding interval reaches the newsvendor quantity. -/
theorem eq_10 (P : CappedBaseStock.DemandLaw) (δ b h y₁ : ℝ) (T : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 < b) (hh : 0 < h)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (hT : 1 ≤ T) :
    (∫ d : CappedBaseStock.DemandPath,
        (∑ t ∈ earlyRounds δ (newsvendor P h b) T,
          (cost P h b (modAimTarget δ b h y₁ d t) - cost P h b (newsvendor P h b)))
          ∂CappedBaseStock.demandPathLaw P) ≤
      max b h * Real.rpow (newsvendor P h b) (1 + 2 / δ) := by sorry

end AIMInventory.UnknownBound
