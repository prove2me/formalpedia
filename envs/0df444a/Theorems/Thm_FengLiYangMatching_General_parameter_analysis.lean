-- Prove2me | Theorems.Thm_FengLiYangMatching_General_parameter_analysis
-- name    : FengLiYangMatching.General.parameter_analysis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T16:53:05.68351+00:00
-- url     : https://prove2.me/theorems/f441f18b-765e-4946-8596-05dcbff56fc0
-- title:
--   Section 3.2 — exact parameter and scalar verification
-- statement:
--   Let $L_k$ be the scalar family of Section 3.2 and let $a^*$ be the selected root of $L_1(a,3/8)=L_{12}(a,3/8)$ in $(0,3/8)$. Then
--
--   $$
--   \exists! a\in(0,3/8):L_1(a,3/8)=L_{12}(a,3/8),\qquad a^*>1/6,
--   $$
--
--   and the selected value is that root. Moreover, for every integer $k\ge1$,
--
--   $$
--   L_k(a^*,3/8)\ge L_1(a^*,3/8)>1089/2000.
--   $$
--
--   These exact scalar inequalities certify the phase parameters used to obtain Theorem 1.1.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018, Section 3.2, pp. 11–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local
open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General
theorem parameter_analysis :
    (∃! a : ℝ, Root a) ∧ Root aStar ∧ (1/6 : ℝ) < aStar ∧
    (∀ k : ℕ, 1 ≤ k → L k aStar (3/8) ≥ L 1 aStar (3/8)) ∧
    L 1 aStar (3/8) > (1089/2000 : ℝ) := by sorry
end FengLiYangMatching.General
