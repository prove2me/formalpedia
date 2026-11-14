-- Prove2me | Theorems.Thm_ConsistentSubmodular_IntervalSelection_le_rowMax_payoff
-- name    : ConsistentSubmodular.IntervalSelection.le_rowMax_payoff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:35.223718+00:00
-- url     : https://prove2.me/theorems/f21e1e49-dd1f-4a2b-910d-344a3e763a95
-- title:
--   Step of Lemma 2 — a row of the payoffs worth at least $\alpha$
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, and let $w_{i,j}=f(O_i\cup R_j)/f(O_j\cup R_j)$ be its payoffs. Let $\alpha\ge0$ be such that every interval-selection instance (for every $N$) has adaptivity gap at least $\alpha$, and suppose every benchmark $f(O_j\cup R_j)$ is positive. Then for every probability vector $\beta$ on $\{0,\dots,m\}$
--   $$\alpha\;\le\;\max_i\sum_j\beta_j\,w_{i,j}.$$
--
--   In the proof of Lemma 2, the reweighted distribution $p_j=(\beta_j/r_j)/Z$ on the interval instance with $r_j=f(O_j\cup R_j)$ and normalizer $Z$ turns the gap bound $\alpha$ into a row of the payoffs worth at least $\alpha$ against $\beta$. This is the hypothesis needed to apply the minimax Lemma 5.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/IntervalSelection.lean#L180-L250 (`ConsistentSubmodular.IntervalSelection.le_rowMax_payoff`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_Minimax

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.IntervalSelection.le_rowMax_payoff {α : ℝ} (hα0 : 0 ≤ α)
    (hgap : ∀ (N : ℕ) (I : IntervalInstance N), α ≤ I.adaptivityGap)
    (hpos : ∀ j, 0 < W.benchmark j) (β : Point W.lastStage) (hβ : IsSimplex β) :
    α ≤ Minimax.rowMax W.payoff β := by sorry
