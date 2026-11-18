-- Prove2me | Theorems.Thm_FengLiYangMatching_General_recovery_in_expectation
-- name    : FengLiYangMatching.General.recovery_in_expectation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T18:20:05.574513+00:00
-- url     : https://prove2.me/theorems/db988f6e-0bf9-4477-85ed-1977c6eda00b
-- title:
--   Lemma 2.3 — recovery bound averaged over shadow histories
-- statement:
--   Let $G$ be a finite simple graph and $M^*$ a maximum matching. Run Algorithm 1 with $0\le a<b=3/8$ and reservation probability $p=5/11$. Let $M^*_{1Y}$ be the optimum edges from early shadow-covered vertices to vertices unmatched in $T_b$, and let $M^*_{YY}$ be the optimum edges entirely among those unmatched vertices. Their cardinalities are integrable, and the recovery-edge counts satisfy
--
--   $$
--   \mathbb E[Z_{XY}+Z_{YY}]\ge\frac3{11}\mathbb E[|M^*_{1Y}|]+\frac25\mathbb E[|M^*_{YY}|].
--   $$
--
--   This is Lemma 2.3 averaged over the accepted-edge history, specialized to the reservation probability chosen in Section 2.3. It supplies the recovery term in the unconditional accounting inequality.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018, Lemma 2.3 and Section 2.3, pp. 8–9, averaged over H_b and specialized to p=5/11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local
open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem recovery_in_expectation {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G)
    (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8) :
    Integrable (fun t => ((M1Y M a (history G (3/8) t)).card : ℝ)) (arrivalLaw G) ∧
    Integrable (fun t => ((MYY M (history G (3/8) t)).card : ℝ)) (arrivalLaw G) ∧
    (∫ w, ZXY G a (3/8) w + ZYY G a (3/8) w ∂sampleLaw G (5/11)) ≥
      (3/11 : ℝ)*(∫ t, ((M1Y M a (history G (3/8) t)).card : ℝ) ∂arrivalLaw G) +
      (2/5 : ℝ)*(∫ t, ((MYY M (history G (3/8) t)).card : ℝ) ∂arrivalLaw G) := by sorry

end FengLiYangMatching.General
