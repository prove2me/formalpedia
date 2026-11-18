-- Prove2me | Theorems.Thm_FengLiYangMatching_General_survival_moments
-- name    : FengLiYangMatching.General.survival_moments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T17:45:31.948309+00:00
-- url     : https://prove2.me/theorems/35faeb97-b404-4a73-bcdb-2af55ad53d40
-- title:
--   Equations (4)–(5) — exact shadow-count survival moments
-- statement:
--   Let $G$ be a finite simple graph, $M^*$ a maximum matching, and $0\le a<b=3/8$. For $e\in M^*$, write $r_e(t)$ for the probability that both endpoints of $e$ are unmatched before $t$ when Greedy runs on $G-e$ with independent uniform arrivals. Let $U_t$ count the edges of $M^*$ with both endpoints free in the shadow matching, and let $M_2^*=M^*\cap(T_b\setminus T_a)$. These counts are integrable and satisfy
--
--   $$
--   \mathbb E[U_t]=\sum_{e\in M^*}(1-t)r_e(t)\qquad(0\le t\le b),
--   $$
--
--   $$
--   \mathbb E[|M_2^*|]=\sum_{e\in M^*}\int_a^b r_e(t)\,dt.
--   $$
--
--   These moment identities connect the concrete shadow execution to the edge-deletion survival experiments used in the competitive-ratio analysis. They are stated without division by the optimum size and include edgeless graphs.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018, Section 2.4, p. 10, Equations (4)–(5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local
open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem survival_moments {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G)
    (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8) :
    (∀ u ∈ Set.Icc (0:ℝ) (3/8),
      Integrable (fun t => U G M t u) (arrivalLaw G) ∧
      (∫ t, U G M t u ∂arrivalLaw G) = ∑ e ∈ M, (1-u)*edgeSurvival G e u) ∧
    Integrable (fun t => ((M2 G M a (3/8) t).card : ℝ)) (arrivalLaw G) ∧
    (∫ t, ((M2 G M a (3/8) t).card : ℝ) ∂arrivalLaw G) =
      ∑ e ∈ M, ∫ s in a..(3/8:ℝ), edgeSurvival G e s := by sorry

end FengLiYangMatching.General
