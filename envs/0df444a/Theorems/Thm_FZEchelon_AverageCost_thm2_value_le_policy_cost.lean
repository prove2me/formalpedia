-- Prove2me | Theorems.Thm_FZEchelon_AverageCost_thm2_value_le_policy_cost
-- name    : FZEchelon.AverageCost.thm2_value_le_policy_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:42:32.485354+00:00
-- url     : https://prove2.me/theorems/192e7375-c43e-4602-afd8-92fd07ee7389
-- title:
--   Proof of Theorem 2, p. 828 — ĝ_n ≤ B_n(· | π) for every measurable feasible policy π
-- statement:
--   Let $\alpha = 1$, let $K, h^d, h^r, p^r > 0$ and $c^d, c^r \ge 0$, and let the demand be nonnegative, continuous and of finite mean. Then for every $n \ge 0$, every physical state ($\tilde y \ge 0$, $x^r \le v^d$) and every measurable policy $\pi$ that is feasible from that state,
--   $$\hat g_n(\tilde y, v^d, x^r) \le B_n(\tilde y, v^d, x^r \mid \pi),$$
--   where $B_n(\cdot \mid \pi)$ is the expected $n$-period cost under $\pi$.
--
--   The finite-horizon value function thus bounds below the $n$-period cost of every history-dependent policy, not only of the Markov policies over which the dynamic program optimizes. In the proof of Theorem 2 this is combined with $\hat g_n/n \to a$ to show that no policy has average cost below $a$.
--
--   **Formalization Note.** The paper assumes all six costs positive (p. 821) and Theorem 2 is proved with $c^d = c^r = 0$; the statement allows $c^d, c^r \ge 0$ and so covers both. The paper passes through a Markov policy with the same $n$-period cost (Dynkin and Yushkevich, result III.1); the statement here is the resulting inequality for every measurable history-dependent policy. $B_n$ is an extended real and $\hat g_n$ is embedded into the extended reals.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 828, proof of Theorem 2, display after 'But, by the definition of ĝ_n'

import Mathlib
import Definitions.Def_FZEchelon_AverageCost_Model
import Definitions.Def_FZEchelon_AverageCost_Policies
import Definitions.Def_FZEchelon_AverageCost_ValueFunctions
open MeasureTheory Filter Topology

namespace FZEchelon.AverageCost

/-- Proof of Theorem 2, p. 828: with `α = 1`, `ĝ_n(ŷ, v^d, x^r) ≤ B_n(ŷ, v^d, x^r | π)` for every
`n`, every physical state and every measurable feasible policy `π`. -/
theorem thm2_value_le_policy_cost (m : Model) (hα : m.α = 1)
    (hK : 0 < m.K) (hcd : 0 ≤ m.cd) (hcr : 0 ≤ m.cr) (hhd : 0 < m.hd) (hhr : 0 < m.hr)
    (hpr : 0 < m.pr)
    [IsProbabilityMeasure m.ν] (hν0 : m.ν (Set.Iio 0) = 0) (hνatom : ∀ t, m.ν {t} = 0)
    (hνint : Integrable id m.ν) :
    ∀ (n : ℕ) (s : SysState m.L), InDomain s →
      ∀ π : Policy (SysState m.L) (ℝ × ℝ), m.SysAdmissible π s →
        ((m.ghat n s : ℝ) : EReal) ≤ m.sysCostN π s n := by sorry

end FZEchelon.AverageCost
