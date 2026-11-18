-- Prove2me | Theorems.Thm_FengLiYangMatching_General_expected_survival_bound
-- name    : FengLiYangMatching.General.expected_survival_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T17:03:39.708081+00:00
-- url     : https://prove2.me/theorems/ee02c10b-b7bc-46bb-9b47-b331afa871d8
-- title:
--   Equation (6) — expected output in terms of edge-deletion survival
-- statement:
--   Let $G$ be a finite simple graph and let $M$ be a maximum matching. Fix $0\le a<3/8$ and run Algorithm 1 with $b=3/8$ and reservation probability $p=5/11$. For each $e\in M$, let $r_e(t)$ denote the probability that both endpoints of $e$ remain unmatched at time $t$ when Greedy is run on $G-e$ with independent uniform arrival times. Then
--
--   $$
--   \mathbb E[\operatorname{ALG}(G)]\ge\frac6{11}\operatorname{OPT}(G)+\sum_{e\in M}\left(\frac12\int_a^{3/8}r_e(t)\,dt-\frac{1-a}{22}r_e(a)-\frac{1-3/8}{10}r_e(3/8)\right).
--   $$
--
--   This is the unnormalized form of the survival-probability lower bound in Equation (6). It includes edgeless graphs and connects the conditional recovery analysis to the convex expansion of the survival functions.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018, Section 2.4, p. 10, Equations (3)–(6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local
open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem expected_survival_bound {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G)
    (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8) :
    (∫ w, ALG G a (3/8) w ∂sampleLaw G (5/11)) ≥ (6/11 : ℝ) * OPT G +
      ∑ e ∈ M, ((1/2 : ℝ) * (∫ t in a..(3/8 : ℝ), edgeSurvival G e t) -
        (1-a)/22 * edgeSurvival G e a -
        (1-(3/8 : ℝ))/10 * edgeSurvival G e (3/8)) := by sorry

end FengLiYangMatching.General
