-- Prove2me | Theorems.Thm_FengLiYangMatching_General_convex_competitive_bound
-- name    : FengLiYangMatching.General.convex_competitive_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T16:53:11.448458+00:00
-- url     : https://prove2.me/theorems/8cd6dcf3-8803-42f5-bff8-c33b545c48c8
-- title:
--   Equation (9) — transferring scalar bounds to a competitive guarantee
-- statement:
--   Fix a phase boundary $0\le a<3/8$, set $b=3/8$ and $p=5/11$, and suppose a real number $c$ satisfies
--
--   $$
--   c\le L_k(a,3/8)\qquad\text{for every integer }k\ge1.
--   $$
--
--   For every finite simple graph $G$, the output of Algorithm 1 is integrable under independent uniform arrivals and independent reservation coins, and
--
--   $$
--   \mathbb E[\operatorname{ALG}(G)]\ge c\operatorname{OPT}(G).
--   $$
--
--   This is the scalar-to-expectation transfer in Equation (9), stated multiplicatively so that edgeless graphs are included. The scalar inequalities are hypotheses; the algorithm's expected guarantee is the conclusion.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018, Sections 2.4–3.2, pp. 10–12, Equations (6), (8), (9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local
open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General
theorem convex_competitive_bound (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8)
    (c : ℝ) (hc : ∀ k : ℕ, 1 ≤ k → c ≤ L k a (3/8)) :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      Integrable (ALG G a (3/8)) (sampleLaw G (5/11)) ∧
      (∫ w, ALG G a (3/8) w ∂sampleLaw G (5/11)) ≥ c * (OPT G : ℝ) := by sorry
end FengLiYangMatching.General
