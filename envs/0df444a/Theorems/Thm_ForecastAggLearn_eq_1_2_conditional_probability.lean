-- Prove2me | Theorems.Thm_ForecastAggLearn_eq_1_2_conditional_probability
-- name    : ForecastAggLearn.eq_1_2_conditional_probability
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:11.761719+00:00
-- url     : https://prove2.me/theorems/1a5ab1df-019c-422d-8a55-5fc35e2792f9
-- title:
--   Eqs. (1)–(2) — the Bayes posteriors $r^*$ and $F_i$ are the conditional probabilities
-- statement:
--   Let $\mu\in[0,1]$ be the prior and let $C_j^0,C_j^1$ be probability measures on measurable spaces $S_j$, $j\in[m]$, with joint law $C$ of $(\omega,s)$ under which the signals are conditionally independent given $\omega$. For $B\subseteq[m]$ let $\operatorname{post}_B$ be the posterior formula $\mu\prod_{j\in B}p^1_j/(\mu\prod_{j\in B}p^1_j+(1-\mu)\prod_{j\in B}p^0_j)$ with $p_j^b=dC_j^b/d(C_j^0+C_j^1)$.
--
--   Then $\operatorname{post}_B$ is measurable, takes values in $[0,1]$, and is a version of $\mathbb P(\omega=1\mid (s_j)_{j\in B})$: for every measurable set $E$ of restricted profiles,
--
--   $$
--   C\bigl(\omega=1,\ (s_j)_{j\in B}\in E\bigr)=\int_{\{(s_j)_{j\in B}\in E\}}\operatorname{post}_B(s)\,dC(\omega,s).
--   $$
--
--   With $B=[m]$ this is $r^*(s)=\mathbb P(\omega=1\mid s_1,\dots,s_m)$ (eq. (1)); with $B=A_i$ it is the expert forecast $F_i(s)=\mathbb P(\omega=1\mid (s_j)_{j\in A_i})$ (eq. (2)). It is what makes the benchmark and the experts' reports in the regret of Theorem 2 the Bayesian quantities of the paper.
--
--   Differences from the source:
--   - encoding: r* and F_i given by the formula in the single-signal posteriors x_j → post via Radon–Nikodym densities against C_j^0 + C_j^1, shown to satisfy the defining identity of P(ω = 1 | (s_j)_{j∈B}); reason: the formula in x_j is 0/0 for μ ∈ {0, 1}; the density form is defined for every μ ∈ [0, 1] and is the same function where (1)–(2) are defined (eq_1_2_formula)
--   - generalization: B = [m] (eq. (1)) and B = A_i (eq. (2)) → every B ⊆ [m]; reason: both equations are the cases B = univ and B = A_i
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §2, eqs. (1)–(2), p.9

import Mathlib
import Definitions.Def_ForecastAggLearn_jointLaw
import Definitions.Def_ForecastAggLearn_post

namespace ForecastAggLearn

open MeasureTheory

/-- **Eqs. (1)–(2): the posteriors are the conditional probabilities.**
Babichenko, Garber, arXiv:1802.07107v1, §2, eqs. (1)–(2), p.9:
`r*(s) = P(ω = 1 | s_1, …, s_m)` and `F_i(s) = P(ω = 1 | (s_j)_{j∈A_i})`.

For every set `B` of signals, `post μ P B` is measurable, `[0, 1]`-valued, and a version of
`P(ω = 1 | (s_j)_{j∈B})` under the joint law: for every measurable set `E` of restricted profiles
`(s_j)_{j∈B}`, `C(ω = 1, (s_j)_{j∈B} ∈ E) = ∫_{(s_j)_{j∈B} ∈ E} post μ P B s dC`.

**Formalization Note.** `B = Finset.univ` gives `r*`, `B = A_i` gives `F_i`. Conditional
probability is expressed by its defining identity, so no conditional-expectation API is needed. -/
theorem eq_1_2_conditional_probability {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (P : (j : Fin m) → Bool → Measure (S j))
    [∀ j b, IsProbabilityMeasure (P j b)] (B : Finset (Fin m)) :
    Measurable (post μ P B) ∧ (∀ s, post μ P B s ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ E : Set ((j : B) → S j), MeasurableSet E →
        jointLaw μ P {x | x.1 = true ∧ (fun j : B => x.2 j) ∈ E} =
          ∫⁻ x in {x : Bool × ((j : Fin m) → S j) | (fun j : B => x.2 j) ∈ E},
            ENNReal.ofReal (post μ P B x.2) ∂(jointLaw μ P) := by sorry

end ForecastAggLearn
