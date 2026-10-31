-- Prove2me | Theorems.Thm_AdaOGD_eq_3_5
-- name    : AdaOGD.eq_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:47.357244+00:00
-- url     : https://prove2.me/theorems/96580da1-9cd5-454c-8d92-0c74c62d8cb7
-- title:
--   Display (3.5) — $\mathrm{I}\le \sqrt{1+\log(T+10)+\log(NT)\log(T+10)}$
-- statement:
--   Let $N,T\ge1$ and let $\{M_i^t\}_{1\le i\le N,1\le t\le T}$ be the step-size draws of Algorithm 3: i.i.d. Geometric($p$) on $\{1,2,\dots\}$ with $p=p_0=1/\log(T+10)$. Then the integrand below is integrable and
--   $$
--   \mathrm{I}=\mathbb E\Big[\sqrt{1+\max_{1\le i\le N,1\le t\le T}\{M_i^t\}}\Big]\ \le\ \sqrt{1+\frac{1+\log(NT)}{p}}=\sqrt{1+\log(T+10)+\log(NT)\log(T+10)}.
--   $$
--
--   The proof of Theorem 3.7 applies this bound to the term $\mathrm{I}$ of (3.4).
--
--   **Formalization Note** The statement involves the draws only, not the game. Lean states the bound by the last expression of the display, which equals the middle one.
--
--   Differences from the source:
--   - encoding: (3.5) inside the proof of Theorem 3.7, with the middle expression $1+(1+\log(NT))/p$ → a statement about the i.i.d. draws alone, bounded by the last expression; reason: the bound uses only the law of the draws; the middle and last expressions are equal for $p=1/\log(T+10)$
--   - encoding: $\mathrm{I}$ → the conclusion also asserts integrability of the integrand; reason: the source takes the expectation as defined; in Lean a non-integrable integrand has integral $0$
-- source:
--   Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning in Strongly Monotone and Exp-Concave Games with Gradient Feedback, arXiv:2310.14085v4, proof of Theorem 3.7, display (3.5), p.18

import Mathlib
import Definitions.Def_AdaOGD_eta

namespace AdaOGD

open MeasureTheory ProbabilityTheory

/-- Display (3.5) (Jordan, Lin & Zhou, arXiv:2310.14085v4, proof of Theorem 3.7, display (3.5),
p.18): for the step-size draws of Algorithm 3 (`{Mᵗᵢ}_{1≤i≤N, 1≤t≤T}` i.i.d. Geometric(`p₀`) with
`p = p₀ = 1/log(T + 10)`),
`I = 𝔼[√(1 + max_{1≤i≤N, 1≤t≤T} Mᵗᵢ)] ≤ √(1 + (1 + log(NT))/p) = √(1 + log(T + 10) + log(NT) log(T + 10))`.

**Formalization Note** The conclusion includes integrability of the integrand. The middle term of
the display equals the last one and is not repeated. -/
theorem eq_3_5 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) {T : ℕ} (hT : 1 ≤ T) (M : Fin N → ℕ → Ω → ℕ) (hM : IsGeomDraws P T M) :
    Integrable (fun ω => Real.sqrt (1 + (maxDraw M T ω : ℝ))) P ∧
      ∫ ω, Real.sqrt (1 + (maxDraw M T ω : ℝ)) ∂P
        ≤ Real.sqrt (1 + Real.log ((T : ℝ) + 10)
            + Real.log ((N : ℝ) * T) * Real.log ((T : ℝ) + 10)) := by sorry

end AdaOGD
