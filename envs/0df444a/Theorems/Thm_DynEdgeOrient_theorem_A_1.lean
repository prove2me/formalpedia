-- Prove2me | Theorems.Thm_DynEdgeOrient_theorem_A_1
-- name    : DynEdgeOrient.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:35:17.583936+00:00
-- url     : https://prove2.me/theorems/537c5265-7624-4a68-8cee-464c60c88882
-- title:
--   Theorem A.1 (log sum inequality): $\sum_i a_i\log(a_i/b_i)\ge a\log(a/b)$
-- statement:
--   Let $a_1,\dots,a_n$ and $b_1,\dots,b_n$ be non-negative real numbers with $a_i=0$ whenever $b_i=0$, and let $a=\sum_{i=1}^na_i$ and $b=\sum_{i=1}^nb_i$. Then
--
--   $$
--   \sum_{i=1}^n a_i\log\frac{a_i}{b_i}\ \ge\ a\log\frac ab ,
--   $$
--
--   with the convention $0\log(0/b)=0$.
--
--   The paper uses it, with signs reversed, to sum the per-node bounds of Lemma 5.2 in the proof of Lemma 5.7.
--
--   **Formalization Note** Natural logarithm; Lean's $\log 0=0$ and $x/0=0$ give the convention $0\log(0/\cdot)=0$.
--
--   Differences from the source:
--   - encoding: non-negative a_i, b_i with no further condition → the extra hypothesis b_i = 0 → a_i = 0; reason: with b_i = 0 < a_i the cited convention makes a_i log(a_i/0) = +∞, so the left side is +∞ and the inequality holds; Lean's log(x/0) = 0 would instead make a = (1, 1), b = (0, 1) a counterexample, so the hypothesis excludes exactly the instances where the source's inequality is trivial
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Theorem A.1, p.28 (pdf p.29), cited from Cover–Thomas [21]

import Mathlib

namespace DynEdgeOrient

/-- **Theorem A.1 (log sum inequality)** (Hiken–Wein, STOC 2027 submission, manuscript sha256
626b4eee…, Appendix A, p.28; cited from Cover–Thomas [21]). For non-negative reals
`a₁, …, aₙ` and `b₁, …, bₙ` with `a = Σ aᵢ`, `b = Σ bᵢ`,
`Σᵢ aᵢ log(aᵢ / bᵢ) ≥ a log(a / b)`.

**Formalization Note.** Natural logarithm (any base gives an equivalent statement). Lean's
`Real.log` is `0` at `0`, and `x / 0 = 0`; the conventions `0 log(0/b) = 0` and `0 log(0/0) = 0`
are the cited ones. The hypothesis `bᵢ = 0 → aᵢ = 0` excludes exactly the instances whose left side
is `+∞` in the cited convention (`aᵢ log(aᵢ/0) = +∞` for `aᵢ > 0`); without it Lean's values make
`a = (1, 1)`, `b = (0, 1)` a counterexample. -/
theorem theorem_A_1 (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤
      ∑ i, a i * Real.log (a i / b i) := by sorry

end DynEdgeOrient
