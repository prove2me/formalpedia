-- Prove2me | Theorems.Thm_FengLiYangMatching_General_survival_recurrence
-- name    : FengLiYangMatching.General.survival_recurrence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T17:08:46.695908+00:00
-- url     : https://prove2.me/theorems/b64edc0c-26ed-4d31-9f19-df50d43e0ea2
-- title:
--   Equation (7) — first matching time decomposition of Greedy survival
-- statement:
--   Let $J$ be a finite simple graph, let $A$ be a set of vertices, and let $P(J,A,t)$ be the probability that every vertex of $A$ is unmatched before time $t$ in Greedy with independent uniform arrival times. For every $t\in[0,1]$,
--
--   $$
--   P(J,A,t)=P(J,A,1)+\sum_{\substack{e\in E(J)\\V(e)\cap A\ne\varnothing}}\int_t^1 P(J-e,A\cup V(e),s)\,ds.
--   $$
--
--   This first-matching-time identity is the recurrence used in Lemma 3.1 to construct a finite nonnegative expansion in powers of $1-t$. It applies also when the graph or the marked set is empty.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018, Section 3.1, p. 11, Equation (7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Process
open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem survival_recurrence {n : ℕ} (J : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    survival J A t = survival J A 1 +
      ∑ e ∈ (graphEdges J).filter (fun e => ∃ v ∈ A, v ∈ e),
        ∫ s in t..(1:ℝ), survival (J.deleteEdges {e}) (A ∪ covered {e}) s := by sorry

end FengLiYangMatching.General
