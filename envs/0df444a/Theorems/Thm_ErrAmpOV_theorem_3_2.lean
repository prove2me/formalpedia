-- Prove2me | Theorems.Thm_ErrAmpOV_theorem_3_2
-- name    : ErrAmpOV.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:29.638408+00:00
-- url     : https://prove2.me/theorems/fdb7a5ce-0134-487e-a7d3-ee5a78ccc16b
-- title:
--   Theorem 3.2 — efficient error reduction for OV
-- statement:
--   Let $0<\alpha<1$ and $c\in\mathbb N$. Then both of the following hold.
--
--   1. Suppose that for every $d$ in the low-dimensional regime there is $C>0$ such that for all sufficiently large $n$, $\mathsf{OV}_{n,d(n)}\in\mathsf{ZPSIZE}_{1/10}[C n^{2-\alpha} d(n)^c]$. Then for every $d$ in the regime and every constant $0<\kappa<2/3$ there are $C,c'>0$ such that for all sufficiently large $n$,
--   $$
--   \mathsf{OV}_{n,d(n)}\in\mathsf{ZPSIZE}_{\delta}\bigl[C n^{2-\alpha\kappa} d(n)^c\bigr],
--   \qquad \delta=2^{-c' n^{2-3\kappa}} .
--   $$
--   2. The same with "for all sufficiently large $n$" replaced by "for infinitely many $n$", in the hypothesis and in the conclusion.
--
--   This is the core of the derandomization: the error drops from a constant to exponentially small in a power of $n$, at no cost beyond a change of the savings exponent.
--
--   Differences from the source:
--   - reading: for all sufficiently large (infinitely many) n and all d := d(n) between ω(log(n)) and n^{o(1)} → two conjuncts: ∀ d, LowDim d → … ∀ᶠ n in atTop, … and ∀ d, LowDim d → … ∃ᶠ n in atTop, …; reason: the parenthesis prints a second version of the theorem; d is a function quantified first, and the threshold or infinite set of n may depend on d
--   - reading: O(n^{2−α} · d^c), O(n^{2−ακ} · d^c), δ := 2^{−Ω(n^{2−3κ})} → hypothesis: ∃ C > 0 per d; conclusion: ∃ C, c′ > 0 after d and κ and before n, with δ = 2^{−c′·n^{2−3κ}}; reason: constants depending on α, c, d, κ but not on n; a per-d constant is the weakest hypothesis. The printed proof picks d(n) = d′(t), which covers only some d; the statement holds for every d by taking a slightly larger block exponent
--   - encoding: Boolean circuits, no gate basis fixed, size = number of gates → ErrAmpOV.Circuit: constant, NOT, AND, OR gates of fan-in at most 2, unbounded fan-out, inputs not counted, a list of output wires; a read of a gate not yet computed returns false; reason: the basis is unspecified on the page; complete fan-in-2 bases differ by a constant factor, and the out-of-range read only gives a free constant false
--   - encoding: ⊥ is a separate output symbol (pp.5–6); Pr over r in {0,1}^{p(n)} → two output wires (abort, value); correct means output [false, f x], ⊥ means output [true, v]; the probability is a count of r : Fin p → Bool over 2^p, with p chosen with the circuit; reason: the page itself encodes ⊥ in output wires; same class up to the abort wire
--   - encoding: Definition 2.1 assumes 1/2 > δ > 0 → ZPDecides takes any real δ; reason: the condition names the class and adds nothing to the predicate; every δ used here satisfies it for large n
--   - encoding: inputs A, B: lists of n vectors in {0,1}^d, a_i · b_j = 0 over ℤ → x : Fin 2 × Fin n × Fin d → Bool, a_i[k] = x (0, i, k), b_j[k] = x (1, j, k), orthogonal iff no coordinate has both entries 1; reason: Lean convention; same 2nd input bits and the same predicate for 0/1 vectors
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Theorem 3.2, p.9 (proof pp.9–11)

import Mathlib
import Definitions.Def_ErrAmpOV_ZPDecides
import Definitions.Def_ErrAmpOV_OV
import Definitions.Def_ErrAmpOV_LowDim

set_option autoImplicit false

namespace ErrAmpOV

/-- Theorem 3.2 (Efficient error reduction for OV), p.9, in both printed versions. Let
`0 < α < 1` and `c ∈ ℕ`.

1. (Sufficiently large `n`.) Suppose that for every dimension function `d` with
   `ω(log n) ≤ d(n) ≤ n^{o(1)}` there is `C > 0` such that for all sufficiently large `n`,
   `OV_{n,d(n)}` has zero-error probabilistic circuits of size at most `C·n^{2−α}·d(n)^c` with
   error at most `1/10`. Then for every such `d` and every `0 < κ < 2/3` there are `C, c' > 0` such
   that for all sufficiently large `n`, `OV_{n,d(n)}` has zero-error probabilistic circuits of size
   at most `C·n^{2−ακ}·d(n)^c` with error at most `2^{−c'·n^{2−3κ}}`.
2. (Infinitely many `n`.) The same with "for all sufficiently large `n`" replaced by "for
   infinitely many `n`", in the hypothesis and in the conclusion.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Theorem 3.2, p.9 (proof pp.9–11).

**Formalization Note.**
* "For all sufficiently large (infinitely many) `n` and all `d := d(n)` between `ω(log n)` and
  `n^{o(1)}`" is `∀ d, LowDim d → ∀ᶠ n in atTop, …` (resp. `∃ᶠ n in atTop`): the threshold (resp.
  the infinite set of `n`) may depend on `d`. The two printed versions are the two conjuncts.
* `O(·)` in the hypothesis is `∃ C > 0` per `d`; `O(·)` and `Ω(·)` in the conclusion are
  `∃ C, c' > 0` chosen after `d` and `κ` and before `n`.
* `n^{2−α}`, `n^{2−ακ}`, `n^{2−3κ}` and `2^{(·)}` are `Real.rpow`; `d(n)^c` is a natural power. -/
theorem theorem_3_2 (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) (c : ℕ) :
    ((∀ d : ℕ → ℕ, LowDim d → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
        ZPDecides (1 / 10) (C * (n : ℝ) ^ (2 - α) * (d n : ℝ) ^ c) (OV n (d n))) →
      ∀ d : ℕ → ℕ, LowDim d → ∀ κ : ℝ, 0 < κ → κ < 2 / 3 →
        ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧ ∀ᶠ n : ℕ in Filter.atTop,
          ZPDecides ((2 : ℝ) ^ (-(c' * (n : ℝ) ^ (2 - 3 * κ))))
            (C * (n : ℝ) ^ (2 - α * κ) * (d n : ℝ) ^ c) (OV n (d n))) ∧
    ((∀ d : ℕ → ℕ, LowDim d → ∃ C : ℝ, 0 < C ∧ ∃ᶠ n : ℕ in Filter.atTop,
        ZPDecides (1 / 10) (C * (n : ℝ) ^ (2 - α) * (d n : ℝ) ^ c) (OV n (d n))) →
      ∀ d : ℕ → ℕ, LowDim d → ∀ κ : ℝ, 0 < κ → κ < 2 / 3 →
        ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧ ∃ᶠ n : ℕ in Filter.atTop,
          ZPDecides ((2 : ℝ) ^ (-(c' * (n : ℝ) ^ (2 - 3 * κ))))
            (C * (n : ℝ) ^ (2 - α * κ) * (d n : ℝ) ^ c) (OV n (d n))) := by sorry

end ErrAmpOV
