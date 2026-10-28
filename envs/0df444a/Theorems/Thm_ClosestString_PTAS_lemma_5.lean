-- Prove2me | Theorems.Thm_ClosestString_PTAS_lemma_5
-- name    : ClosestString.PTAS.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T16:17:35.258218+00:00
-- url     : https://prove2.me/theorems/3e8a3917-65c3-454a-9406-ccfbaf421359
-- title:
--   Lemma 5 — additive Chernoff bounds: Pr(X > µ + εn) < exp(−nε²/3) and Pr(X < µ − εn) ≤ exp(−nε²/2) for 0 < ε ≤ 1
-- statement:
--   Let $X_1,\dots,X_N$ be independent random 0-1 variables, $X_i$ taking $1$ with probability $p_i\in[0,1]$, $X=\sum_iX_i$ and $\mu=\mathbb E[X]$. Then for every $0<\varepsilon\le1$:
--
--   1. $$\Pr(X>\mu+\varepsilon N)<\exp\Big(-\tfrac13N\varepsilon^2\Big)\quad\text{and}\quad \Pr(X\ge\mu+\varepsilon N)\le\exp\Big(-\tfrac13N\varepsilon^2\Big);$$
--   2. $$\Pr(X\le\mu-\varepsilon N)\le\exp\Big(-\tfrac12N\varepsilon^2\Big).$$
--
--   The paper uses this lemma three times: for the randomized rounding of Lemma 6 (p. 6) and for the two tails (11) and (12) of the sampled distance in the proof of Fact 2 (p. 11).
--
--   Differences from the source:
--
--   - generalization: Xi as in Lemma 4, with 0 < pi < 1 → 0 ≤ p_i ≤ 1; reason: the paper applies Lemma 5 to variables whose probability may be 0 or 1 (rounding probabilities x̄_{j,a}, p. 6; d^P(s*, t′)/|P| in (11)–(12)); the printed range is a special case
--   - generalization: (1) Pr(X > µ + εn) < …; (2) Pr(X < µ − εn) ≤ … → (1) both Pr(X > µ + εN) < … and Pr(X ≥ µ + εN) ≤ …; (2) Pr(X ≤ µ − εN) ≤ …; reason: the paper's uses are non-strict events (p. 6 "≥ d0 + ε′|P| − …", (11) "≤ µ − ε|R|", (12) "≥ d(s∗, ti) + ε|P|"); the strict (1) is kept as printed and the event of the printed (2) is contained in the posed one
--   - encoding: independent random 0-1 variables X_i taking 1 with probability p_i → measurable X_i : Ω → ℝ, iIndepFun, P(X_i = 1) = p_i and P(X_i = 0) = 1 − p_i; reason: the two point probabilities force X_i ∈ {0,1} almost surely; same instances
--   - encoding: n variables → N variables (Fin N); reason: renaming only
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 5, Lemma 5

import Mathlib

namespace ClosestString.PTAS

open MeasureTheory ProbabilityTheory

/-- **Lemma 5** (Li, Ma & Wang, arXiv:cs/0002012v1, p. 5), for independent 0-1 random variables
`X_1, …, X_N` with `P(X_i = 1) = p_i ∈ [0, 1]`, `X = Σ X_i`, `µ = E[X]` and `0 < ε ≤ 1`:
(1) `Pr(X > µ + εN) < exp(−Nε²/3)` and `Pr(X ≥ µ + εN) ≤ exp(−Nε²/3)`;
(2) `Pr(X ≤ µ − εN) ≤ exp(−Nε²/2)`. -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {N : ℕ} (X : Fin N → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X Pr)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hX_ber : ∀ i, Pr.real {ω | X i ω = 1} = p i ∧ Pr.real {ω | X i ω = 0} = 1 - p i)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Pr.real {ω | (∫ ω', ∑ i, X i ω' ∂Pr) + ε * N < ∑ i, X i ω} <
        Real.exp (-(1 / 3) * N * ε ^ 2) ∧
      Pr.real {ω | (∫ ω', ∑ i, X i ω' ∂Pr) + ε * N ≤ ∑ i, X i ω} ≤
        Real.exp (-(1 / 3) * N * ε ^ 2) ∧
      Pr.real {ω | ∑ i, X i ω ≤ (∫ ω', ∑ i, X i ω' ∂Pr) - ε * N} ≤
        Real.exp (-(1 / 2) * N * ε ^ 2) := by sorry

end ClosestString.PTAS
