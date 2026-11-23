-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_Supplement_chernoff_bounds
-- name    : BestBothWorlds.SAO.Supplement.chernoff_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:16:51.167459+00:00
-- url     : https://prove2.me/theorems/3bf80102-8ab1-4780-a91b-05fc345be1ab
-- title:
--   Theorem 3.2 — Chernoff Bounds for independent bounded summands
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, and let $X_1,\ldots,X_n$ be mutually independent measurable real random variables taking values in $[0,1]$. The variables need not have identical distributions. Write $S=\sum_{t=1}^n X_t$ for their sum and $\mu=\mathbb E_P[S]$ for its expectation. For every real $C>1$,
--
--   $$
--   P\!\left(\lvert S-\mu\rvert>C\max\{1,\sqrt{\mu}\}\right)<2\exp(-C/3).
--   $$
--
--   This is the single two-sided Chernoff inequality used in the paper's two-arm warm-up (§3). It is a companion theorem, independent of the SAO regret goal in §4. Boundedness on a probability space ensures that every summand and the sum are integrable. The strict event and strict probability bound are both retained, including when $\mu=0$; the empty sum at $n=0$ is also included.
--
--   **Formalization Note** The local name $S$ denotes the paper's random variable $X$, to distinguish the sum from the indexed family. No bandit model, identical-distribution assumption, Bernoulli assumption, or positive-mean condition enters the statement.
--
--   Differences from the source:
--   - encoding: Independent random variables with values in [0,1] and their probability → Measurable real functions on an arbitrary probability space, iIndepFun, pointwise Set.Icc bounds, and P.real of the event; reason: The standard measurable-random-variable convention; iIndepFun means mutual independence, and the finite event measure is the same real probability
--   - encoding: Indices t = 1, …, n; X = Σ Xt and µ = E[X] → Fin n indices t = 0, …, n−1, with local lets S = ∑ t, X t and μ = ∫ S dP; reason: A bijective relabelling and the same sum and expectation; no division by n or positive-mean hypothesis is introduced
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 7, §3.2, Theorem 3.2, eq. (4)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BestBothWorlds.SAO.Supplement

/-- Theorem 3.2 (Chernoff Bounds), Bubeck--Slivkins, arXiv:1202.4473v1, p. 7,
eq. (4). The `n` summands are mutually independent and need not have the same law.
`Fin n` relabels the paper's indices `1, ..., n`; `S` is the sum, not the average.
Measurability and the pointwise `[0,1]` bounds imply integrability of every summand
and of `S` on the probability space, so the expectation has no default-value case.
The statement includes `n = 0` and mean zero, and both inequalities are strict. -/
theorem chernoff_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ)
    (hmeas : ∀ t, Measurable (X t))
    (hind : iIndepFun X P)
    (hbound : ∀ t ω, X t ω ∈ Set.Icc (0 : ℝ) 1)
    (C : ℝ) (hC : 1 < C) :
    let S : Ω → ℝ := fun ω => ∑ t, X t ω
    let μ : ℝ := ∫ ω, S ω ∂P
    P.real {ω | C * max 1 (Real.sqrt μ) < |S ω - μ|} <
      2 * Real.exp (-C / 3) := by sorry

end BestBothWorlds.SAO.Supplement
