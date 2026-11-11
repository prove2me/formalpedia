-- Prove2me | Theorems.Thm_ForestRoundingNSW_Rounding_eq_11
-- name    : ForestRoundingNSW.Rounding.eq_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:51:10.963709+00:00
-- url     : https://prove2.me/theorems/cbb5cd18-068c-4e1f-9fc0-b3c43e389ca7
-- title:
--   §3.2, Eq. (11) — ((1 − t)u + tw)/(u^{1−t}w^t) ≤ (1 + t)/2^t ≤ 2/(e ln 2) = C for u ≤ w ≤ 2u
-- statement:
--   Let $u>0$, $u\le w\le 2u$ and $0<t<1$. Then
--   $$\frac{(1-t)u+tw}{u^{1-t}w^{t}}\;\le\;\frac{1+t}{2^{t}}\;\le\;\frac{2}{e\ln 2}=C .$$
--
--   This is the last-step inequality in the proof of Lemma 3.2: the final Bernoulli choice of Algorithm 1 loses at most the factor $C$ between the arithmetic and the geometric value.
--
--   Differences from the source:
--   - reading: u = max{f(A), b} with b > 0, so u > 0 → the hypothesis 0 < u; reason: the display's own hypotheses; u > 0 is what makes u^{1−t} meaningful
--   - encoding: 2^t, u^{1−t}, w^t, e → real powers (rpow) and Real.exp 1; reason: Lean convention; same values
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 21, §3.2, Eq. (11)

import Mathlib
import Definitions.Def_ForestRoundingNSW_Rounding_BalancedRounding

namespace ForestRoundingNSW.Rounding

theorem eq_11 (u w t : ℝ) (hu : 0 < u) (huw : u ≤ w) (hw : w ≤ 2 * u) (ht0 : 0 < t)
    (ht1 : t < 1) :
    ((1 - t) * u + t * w) / (u ^ (1 - t) * w ^ t) ≤ (1 + t) / (2 : ℝ) ^ t ∧
    (1 + t) / (2 : ℝ) ^ t ≤ 2 / (Real.exp 1 * Real.log 2) ∧
    2 / (Real.exp 1 * Real.log 2) = C := by sorry

end ForestRoundingNSW.Rounding
