-- Prove2me | Theorems.Thm_BauerleRiederMDP_RegimeSwitching_theorem_4_3_1
-- name    : BauerleRiederMDP.RegimeSwitching.theorem_4_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:25:26.206312+00:00
-- url     : https://prove2.me/theorems/ebda14c1-127d-49c7-8b44-6bc162d5f304
-- title:
--   Theorem 4.3.1 — one-period consumption-investment: optimal pair iff no arbitrage (corrected: b) under no arbitrage)
-- statement:
--   Consider an investor with interest rate $i\ge0$ and a relative risk $R\in\mathbb R^d$ of the risky assets with $R>-1$ a.s. and $\mathbb E\|R\|<\infty$. Let $U_c$ and $U_p$ be utility functions with $\operatorname{dom}U_c=\operatorname{dom}U_p=[0,\infty)$, and for $x\ge0$ let
--
--   $$
--   v(x)=\sup_{(c,a)\in D(x)}\Big\{U_c(c)+\mathbb E\,U_p\big((1+i)(x-c+a\cdot R)\big)\Big\}
--   $$
--
--   be the value of the one-period consumption-investment problem, where $D(x)$ is the set of pairs with $0\le c\le x$ and nonnegative next wealth a.s. Then:
--
--   1. There are no arbitrage opportunities if and only if there is a measurable $f^*:[0,\infty)\to\mathbb R_+\times\mathbb R^d$ with $f^*(x)\in D(x)$ and
--   $$u\big(x,f^*(x)\big)=v(x),\qquad x\ge0.$$
--   2. If there are no arbitrage opportunities, then $v$ is finite on $[0,\infty)$ and strictly increasing, strictly concave and continuous there.
--
--   The theorem is the one-period building block of the structure theorems for consumption-investment problems: it supplies the maximizers and preserves the class of utility-like value functions.
--
--   **Formalization Note** $v$ takes values in $[-\infty,\infty]$; part 2 is stated for its real value after asserting finiteness.
--
--   Differences from the source:
--   - correction: b) v is strictly increasing, strictly concave and continuous on dom U_p, for every pair of utility functions → b) under the hypothesis that there are no arbitrage opportunities; reason: without it b) is false: U_p(x) = √x, any U_c, one stock, i = 0, R ∈ {0, u − 1} with u > 1; every a ≥ 0 is admissible and v ≡ +∞ (paper.md correction 2; the book's proof uses the compactness from a))
--   - reading: a measurable function f*: dom U_p → A with u(x, f*(x)) = v(x) → a measurable f : ℝ → ℝ × ℝ^d with f(x) ∈ D(x) and u(x, f(x)) = v(x) for x ≥ 0; reason: f* is a maximizer of the problem, so its values are admissible; a measurable map on [0, ∞) extends measurably to ℝ
--   - encoding: v real-valued, strictly increasing, strictly concave and continuous → v ∈ EReal is ≠ ⊤, ≠ ⊥ on [0, ∞) and its real value satisfies IsUtilityFunction on Ici 0; reason: v can be +∞ without no arbitrage, so it is defined in EReal; the added finiteness is part of the book's claim that v is a real function
--   - encoding: no arbitrage opportunities in the one-period market → NoArbitrageLaw μ: φ·z ≥ 0 μ-a.e. ⇒ φ·z = 0 μ-a.e., for the law μ of R; reason: equivalent one-period form (Theorem 3.1.5; Assumption (FM)(i), p.101); depends only on the law of R
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.3.1, p.95 (PDF p.109); problem on p.94 (PDF p.108); assumption IE‖R‖ < ∞, p.76 (PDF p.90)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_IsUtilityFunction
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_NoArbitrageLaw
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_onePeriodV
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BauerleRiederMDP.RegimeSwitching

/-- **Theorem 4.3.1** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.95, PDF p.109; problem on p.94, PDF p.108). Let `U_c` and `U_p` be
utility functions with `dom U_c = dom U_p = [0, ∞)`, and consider the one-period
consumption-investment problem `v(x) = sup_{(c,a) ∈ D(x)} u(x, c, a)` with interest rate
`i ≥ 0` and a relative risk `R` of law `μ`, `R > −1` a.s. and `𝔼‖R‖ < ∞`. Then:
a) there are no arbitrage opportunities if and only if there is a measurable
`f* : dom U_p → A` with `u(x, f*(x)) = v(x)` for `x ∈ dom U_p`;
b) (corrected: under no arbitrage) `v` is finite, strictly increasing, strictly concave and
continuous on `dom U_p`.

**Formalization Note.** In a), `f*(x)` is required to lie in `D(x)` (a maximizer of the problem);
`f*` is a measurable map on `ℝ` (any measurable map on `[0, ∞)` extends to one). Part b) is printed
without the no-arbitrage hypothesis, but it is false then: with `U_p(x) = √x`, one stock, `i = 0`
and `R ∈ {0, u − 1}` (`u > 1`), every `a ≥ 0` is admissible and `v ≡ +∞`. The utility properties
of `v` are stated for its real value, after showing that `v` is finite. -/
theorem theorem_4_3_1 {d : ℕ} (μ : ProbabilityMeasure (Fin d → ℝ)) (i : ℝ) (hi : 0 ≤ i)
    (hR : ∀ᵐ z ∂(μ : Measure (Fin d → ℝ)), ∀ k, -1 < z k)
    (hint : Integrable (fun z : Fin d → ℝ => ∑ k, |z k|) (μ : Measure (Fin d → ℝ)))
    (Uc Up : ℝ → ℝ) (hUc : IsUtilityFunction Uc (Set.Ici 0))
    (hUp : IsUtilityFunction Up (Set.Ici 0)) :
    (NoArbitrageLaw (μ : Measure (Fin d → ℝ)) ↔
      ∃ f : ℝ → ℝ × (Fin d → ℝ), Measurable f ∧ ∀ x, 0 ≤ x →
        f x ∈ onePeriodD (μ : Measure (Fin d → ℝ)) i x ∧
        onePeriodU (μ : Measure (Fin d → ℝ)) i Uc Up x (f x) =
          onePeriodV (μ : Measure (Fin d → ℝ)) i Uc Up x) ∧
    (NoArbitrageLaw (μ : Measure (Fin d → ℝ)) →
      (∀ x, 0 ≤ x → onePeriodV (μ : Measure (Fin d → ℝ)) i Uc Up x ≠ ⊤ ∧
          onePeriodV (μ : Measure (Fin d → ℝ)) i Uc Up x ≠ ⊥) ∧
      IsUtilityFunction (fun x => (onePeriodV (μ : Measure (Fin d → ℝ)) i Uc Up x).toReal)
        (Set.Ici 0)) := by sorry

end BauerleRiederMDP.RegimeSwitching
