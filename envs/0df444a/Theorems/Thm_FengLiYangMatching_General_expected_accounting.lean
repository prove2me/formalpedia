-- Prove2me | Theorems.Thm_FengLiYangMatching_General_expected_accounting
-- name    : FengLiYangMatching.General.expected_accounting
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T17:45:32.886666+00:00
-- url     : https://prove2.me/theorems/22945b80-8b50-44f4-b281-fb2766941f89
-- title:
--   Equation (3) — recovery and vertex accounting in expectation
-- statement:
--   Let $G$ be a finite simple graph and let $M^*$ be a maximum matching. Run Algorithm 1 with $0\le a<3/8$, $b=3/8$ and reservation probability $p=5/11$. Let $U_t$ be the number of edges of $M^*$ with both endpoints unmatched in the shadow matching before $t$, and let $M_2^*=M^*\cap(T_b\setminus T_a)$. Then
--
--   $$
--   \mathbb E[\operatorname{ALG}(G)]\ge\frac6{11}\operatorname{OPT}(G)+\frac12\mathbb E[|M_2^*|]-\frac1{22}\mathbb E[U_a]-\frac1{10}\mathbb E[U_b].
--   $$
--
--   This is the unconditional recovery-accounting bound preceding the survival-probability substitutions. It isolates the contribution of retained optimum edges and the costs associated with unmatched optimum edges.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018, Section 2.4, p. 10, Equation (3); derived in Section 2.3, p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local
open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem expected_accounting {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G)
    (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8) :
    (∫ w, ALG G a (3/8) w ∂sampleLaw G (5/11)) ≥ (6/11 : ℝ) * OPT G +
      (1/2 : ℝ) * (∫ t, ((M2 G M a (3/8) t).card : ℝ) ∂arrivalLaw G) -
      (1/22 : ℝ) * (∫ t, U G M t a ∂arrivalLaw G) -
      (1/10 : ℝ) * (∫ t, U G M t (3/8) ∂arrivalLaw G) := by sorry

end FengLiYangMatching.General
