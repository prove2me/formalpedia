-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_observation_4_2
-- name    : CNFLearning873.Valiant.observation_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:08:01.240391+00:00
-- url     : https://prove2.me/theorems/97e1bcde-8f5b-46d6-b3ce-515b7cce5a4f
-- title:
--   Observation 4.2 — three local lemma estimates
-- statement:
--   For integers $k\ge100,d\ge1$ and any real $t\ge1$, suppose condition (2) holds. Then all three estimates are valid:
--
--   $$\log_2(dk)<k-\log_2k-6,$$
--   $$\log_2(dk)\le kt/(1+t)-3,$$
--   $$dk\,2^{1-kt/(1+t)}\le1/4.$$
--
--   These estimates retain the strict inequality in the first clause and the real power in the third. They provide the quantitative consequences of the precise threshold used throughout the section.
--
--   Differences from the source:
--   - encoding: log is base two and the exponent is real → log₂ x = Real.log x / Real.log 2 and real exponentiation; reason: same logarithm and power, with positive arguments from the hypotheses
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Observation 4.2, printed p.13 = 1-based PDF p.13

import Definitions.Def_CNFLearning873_Valiant_Thresholds

namespace CNFLearning873.Valiant

/-- Observation 4.2, all three estimates (3), p.13 = PDF p.13. -/
theorem observation_4_2 (k d : ℕ) (t : ℝ) (hk : 100 ≤ k) (hd : 1 ≤ d)
    (ht : 1 ≤ t) (hLLL : LLLCondition k d t) :
    log₂ ((d : ℝ) * k) < (k : ℝ) - log₂ k - 6 ∧
    log₂ ((d : ℝ) * k) ≤ (k : ℝ) * t / (1 + t) - 3 ∧
    (d : ℝ) * k * (2 : ℝ) ^ (1 - (k : ℝ) * t / (1 + t)) ≤ 1 / 4 := by sorry

end CNFLearning873.Valiant
