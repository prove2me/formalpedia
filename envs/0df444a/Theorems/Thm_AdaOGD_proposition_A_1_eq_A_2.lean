-- Prove2me | Theorems.Thm_AdaOGD_proposition_A_1_eq_A_2
-- name    : AdaOGD.proposition_A_1_eq_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:55.853568+00:00
-- url     : https://prove2.me/theorems/59cd57bd-ee15-455f-9161-77145ad8b28b
-- title:
--   Proposition A.1, (A.2) — $1\le\mathbb E[\bar X_n]\le(1+\log n)/p_0$
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be i.i.d. Geometric($p_0$) random variables on $\{1,2,\dots\}$ with $p_0\in(0,1)$, and let $\bar X_n=\max_{1\le i\le n}X_i$. Then $\bar X_n$ is integrable and
--   $$
--   1\ \le\ \mathbb E[\bar X_n]\ \le\ \frac{1+\log n}{p_0}.
--   $$
--
--   With $p_0=1/\log(T+10)$ and $n=NT$ this gives the bounds (3.5) and (3.6) on the expected maximum draw of MA-AdaOGD.
--
--   **Formalization Note** The $n$ variables are indexed by an arbitrary nonempty finite type $\iota$, with $n=|\iota|$.
--
--   Differences from the source:
--   - encoding: $X_1,\dots,X_n$ → a family indexed by a nonempty finite type $\iota$ with $n=|\iota|$; reason: any relabelling of $\{1,\dots,n\}$; $n\ge1$ as in the source
--   - encoding: $\mathbb E[\bar X_n]$ → the conclusion also asserts integrability of the integrand; reason: the source takes the expectation as defined; in Lean a non-integrable integrand has integral $0$
-- source:
--   Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning in Strongly Monotone and Exp-Concave Games with Gradient Feedback, arXiv:2310.14085v4, Appendix A, Proposition A.1, display (A.2), pp.36–37

import Mathlib
import Definitions.Def_AdaOGD_eta

namespace AdaOGD

open MeasureTheory ProbabilityTheory

/-- Proposition A.1, (A.2) (Jordan, Lin & Zhou, arXiv:2310.14085v4, Appendix A, p.36): let
`X₁, …, Xₙ` be `n ≥ 1` i.i.d. Geometric(`p₀`) random variables on `{1, 2, …}` with `p₀ ∈ (0, 1)`
and `X̄ₙ = max_{1≤i≤n} Xᵢ`. Then `1 ≤ 𝔼[X̄ₙ] ≤ (1 + log n)/p₀`.

**Formalization Note** The `n` variables are indexed by any finite nonempty type `ι` with `n` its
cardinality. The conclusion includes integrability of `X̄ₙ`, so that `𝔼[X̄ₙ]` is the Bochner integral
of an integrable function. -/
theorem proposition_A_1_eq_A_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₀1 : p₀ < 1) {ι : Type*} [Fintype ι]
    [Nonempty ι] (X : ι → Ω → ℕ) (hind : iIndepFun X P) (hgeom : ∀ i, IsGeometric P p₀ (X i)) :
    Integrable (fun ω => ((Finset.univ.sup fun i => X i ω : ℕ) : ℝ)) P ∧
      1 ≤ ∫ ω, ((Finset.univ.sup fun i => X i ω : ℕ) : ℝ) ∂P ∧
      ∫ ω, ((Finset.univ.sup fun i => X i ω : ℕ) : ℝ) ∂P
        ≤ (1 + Real.log (Fintype.card ι)) / p₀ := by sorry

end AdaOGD
