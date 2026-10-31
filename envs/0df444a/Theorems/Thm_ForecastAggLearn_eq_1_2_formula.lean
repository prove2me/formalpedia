-- Prove2me | Theorems.Thm_ForecastAggLearn_eq_1_2_formula
-- name    : ForecastAggLearn.eq_1_2_formula
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:08.755826+00:00
-- url     : https://prove2.me/theorems/a9a4d622-670b-4a14-957c-96a119eded7b
-- title:
--   Eqs. (1)–(2) — the Bayesian formula for aggregating conditionally independent signals
-- statement:
--   Let $0<\mu<1$, let the conditional laws $C_j^0,C_j^1$ be probability measures, and let $x_j(s_j)=\mathbb P(\omega=1\mid s_j)$ be the single-signal posteriors. For a set $B\subseteq[m]$ and a signal profile $s$ at which the denominator below is nonzero,
--
--   $$
--   \mathbb P\bigl(\omega=1\mid (s_j)_{j\in B}\bigr)=\frac{(1-\mu)^{|B|-1}\prod_{j\in B}x_j(s_j)}{(1-\mu)^{|B|-1}\prod_{j\in B}x_j(s_j)+\mu^{|B|-1}\prod_{j\in B}(1-x_j(s_j))}.
--   $$
--
--   For $B=[m]$ this is eq. (1) for $r^*(s)$, and for $B=A_i$ it is eq. (2) for the forecast $F_i(s)$ of expert $i$. It is the classical aggregation formula for conditionally independent signals, and the starting point of the log-likelihood linearization.
--
--   **Formalization Note** Both posteriors are the density formula `post` (see eq_1_2_conditional_probability); values $x_j(s_j)\in\{0,1\}$ are allowed; the exponent $|B|-1$ is an integer, so $B=\emptyset$ gives the prior $\mu$.
--
--   Differences from the source:
--   - reading: denominator of (2) has Π_{j∈A_j} → Π_{j∈A_i}; reason: misprint: the index j is bound by the product, the set is A_i as in the numerator
--   - encoding: (1)–(2) without a domain → 0 < μ < 1 and a nonzero denominator; posteriors are post μ P B, x_j = post μ P {j}; reason: the printed quotients have a zero denominator outside this domain or, for μ ∈ {0, 1} and |B| ≥ 2, are 0/0 off a null set (for |B| = 1 the formula is the tautology x_j = x_j); it excludes only undefined cases
--   - generalization: B = [m] and B = A_i → every B ⊆ [m]; reason: (1) and (2) are the cases B = univ and B = A_i
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §2, eqs. (1)–(2), p.9

import Mathlib
import Definitions.Def_ForecastAggLearn_post

namespace ForecastAggLearn

open MeasureTheory

/-- **Eqs. (1)–(2): the Bayesian aggregation formula.**
Babichenko, Garber, arXiv:1802.07107v1, §2, eqs. (1)–(2), p.9: with `x_j(s_j) = P(ω = 1 | s_j)`,

`P(ω = 1 | (s_j)_{j∈B}) = (1 − µ)^{|B|−1} Π_{j∈B} x_j(s_j) /
  ((1 − µ)^{|B|−1} Π_{j∈B} x_j(s_j) + µ^{|B|−1} Π_{j∈B} (1 − x_j(s_j)))`,

for `B = [m]` (eq. (1), `r*`) and `B = A_i` (eq. (2), `F_i`).

**Formalization Note.** `x_j(s_j) = post μ P {j} s`, which may be `0` or `1`. The formula is stated
where it is defined: `0 < μ < 1` and a nonzero denominator. The exponent `|B| − 1` is an integer
(`zpow`), so `B = ∅` gives the prior. The denominator of (2) prints `Π_{j∈A_j}`; it is `Π_{j∈A_i}`. -/
theorem eq_1_2_formula {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (P : (j : Fin m) → Bool → Measure (S j))
    [∀ j b, IsProbabilityMeasure (P j b)] (B : Finset (Fin m)) (s : (j : Fin m) → S j)
    (hD : (1 - μ) ^ ((B.card : ℤ) - 1) * (∏ j ∈ B, post μ P {j} s) +
      μ ^ ((B.card : ℤ) - 1) * (∏ j ∈ B, (1 - post μ P {j} s)) ≠ 0) :
    post μ P B s =
      ((1 - μ) ^ ((B.card : ℤ) - 1) * (∏ j ∈ B, post μ P {j} s)) /
        ((1 - μ) ^ ((B.card : ℤ) - 1) * (∏ j ∈ B, post μ P {j} s) +
          μ ^ ((B.card : ℤ) - 1) * (∏ j ∈ B, (1 - post μ P {j} s))) := by sorry

end ForecastAggLearn
