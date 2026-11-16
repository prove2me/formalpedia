-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_lemma_C_1
-- name    : EliasGlobalClock.LowerBound.Supplement.lemma_C_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T07:37:33.027327+00:00
-- url     : https://prove2.me/theorems/2ee765ba-03e9-483e-bcda-666de0bffaba
-- title:
--   Lemma C.1 — population sensitivity of the singleton probability
-- statement:
--   For $n\ge1$ and $p\in[0,1]$ let $q_n(p)=np(1-p)^{n-1}$ be the probability that exactly one of $n$ players transmits when each transmits independently with probability $p$ (so $q_1(p)=p$). For integers $N\ge2$ and $n\ge1$ with $|n-N|\le N/2$, and every $p\in[0,1]$,
--   $$|q_n(p)-q_N(p)|\le\frac{4\,|n-N|}{N}.$$
--
--   The bound lets the analysis of a test or of an exploitation slot use a fixed reference population while players depart and arrive.
--
--   Differences from the source: none.
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.29 / PDF p.30, Lemma C.1 (proof printed p.30 / PDF p.31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_algorithmTwo

namespace EliasGlobalClock.LowerBound.Supplement

/-- Lemma C.1 (Population sensitivity; printed p.29 / PDF p.30). For integers `N ≥ 2`,
`n ≥ 1` with `|n − N| ≤ N/2` and every `p ∈ [0,1]`,
`|q_n(p) − q_N(p)| ≤ 4|n − N|/N`, where `q_n(p) = n p (1−p)^{n−1}`. -/
theorem lemma_C_1 (N n : ℕ) (hN : 2 ≤ N) (hn : 1 ≤ n)
    (hnN : |(n : ℝ) - N| ≤ (N : ℝ) / 2) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |singletonProb n p - singletonProb N p| ≤ 4 * |(n : ℝ) - N| / N := by sorry

end EliasGlobalClock.LowerBound.Supplement
