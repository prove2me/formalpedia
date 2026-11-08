-- Prove2me | Theorems.Thm_ErrAmpOV_theorem_3_1
-- name    : ErrAmpOV.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:40.454224+00:00
-- url     : https://prove2.me/theorems/af111b90-49da-43e9-a765-16817b4d700c
-- title:
--   Theorem 3.1 — efficient derandomization of zero-error circuits for low-dimensional OV
-- statement:
--   Let $0<\alpha<1$ and $c\in\mathbb N$. Suppose that for every dimension function $d$ with $\omega(\log n)\le d(n)\le n^{o(1)}$ and all sufficiently large $n$,
--   $$
--   \mathsf{OV}_{n,d(n)}\in\mathsf{ZPSIZE}_{1/10}\bigl[n^{2-\alpha}\cdot d(n)^c\bigr].
--   $$
--   Then for every such $d$ and all sufficiently large $n$,
--   $$
--   \mathsf{OV}_{n,d(n)}\in\mathsf{SIZE}\bigl[n^{2-\alpha/4}\cdot d(n)^c\bigr].
--   $$
--
--   Here $\mathsf{ZPSIZE}_{1/10}[S]$ asks for a probabilistic circuit of size at most $S$ that on every input and every random string outputs the right answer or $\bot$, and outputs the right answer with probability at least $9/10$. $\mathsf{SIZE}[S]$ asks for a deterministic circuit of size at most $S$ correct on every input.
--
--   So truly subquadratic zero-error circuits for low-dimensional OV give truly subquadratic deterministic circuits, and the OV conjecture for the two circuit classes is the same statement up to the savings. This is the formal version of Theorem 1.1 of the paper.
--
--   **Formalization Note** $n^{2-\alpha}$ and $n^{2-\alpha/4}$ are `Real.rpow`, and $d(n)^c$ is a natural power.
--
--   Differences from the source:
--   - encoding: Suppose that there exists 0 < α < 1 and c ∈ N such that H(α, c). Then C(α, c) → parameters α, c and the implication H(α, c) → C(α, c); reason: the same theorem: α and c are the same on both sides
--   - reading: for all sufficiently large n and all d := d(n) between ω(log(n)) and n^{o(1)} → ∀ d : ℕ → ℕ, LowDim d → ∀ᶠ n in atTop, …, where LowDim d is d(n)/log n → ∞ and log d(n)/log n → 0; reason: no single n has a regime, so d is a function quantified first; the threshold may depend on d, which is the weakest hypothesis and the natural conclusion
--   - reading: ZPSIZE_{1/10}[n^{2−α} · d^c] and SIZE[n^{2−α/4} · d^c], with no O(·) on p.9, while the proof on p.11 ends at O(n^{2−α/4} · d^c) → exact bounds on both sides, size ≤ n^{2−α}·d(n)^c and size ≤ n^{2−α/4}·d(n)^c; reason: as printed in the statement, and Definition 2.1 says "size at most S(n)"; the exact conclusion follows by using κ in (1/4, 1/3) in place of the proof's κ = 1/4, so nothing is weakened
--   - encoding: Boolean circuits, no gate basis fixed, size = number of gates → ErrAmpOV.Circuit: constant, NOT, AND, OR gates of fan-in at most 2, unbounded fan-out, inputs not counted, a list of output wires; a read of a gate not yet computed returns false; reason: the basis is unspecified on the page; complete fan-in-2 bases differ by a constant factor, and the out-of-range read only gives a free constant false
--   - encoding: ⊥ is a separate output symbol (pp.5–6); Pr over r in {0,1}^{p(n)} → two output wires (abort, value); correct means output [false, f x], ⊥ means output [true, v]; the probability is a count of r : Fin p → Bool over 2^p, with p chosen with the circuit; reason: the page itself encodes ⊥ in output wires; same class up to the abort wire
--   - encoding: Definition 2.1 assumes 1/2 > δ > 0 → ZPDecides takes any real δ; reason: the condition names the class and adds nothing to the predicate; every δ used here satisfies it for large n
--   - encoding: inputs A, B: lists of n vectors in {0,1}^d, a_i · b_j = 0 over ℤ → x : Fin 2 × Fin n × Fin d → Bool, a_i[k] = x (0, i, k), b_j[k] = x (1, j, k), orthogonal iff no coordinate has both entries 1; reason: Lean convention; same 2nd input bits and the same predicate for 0/1 vectors
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Theorem 3.1, p.9 (proof p.11)

import Mathlib
import Definitions.Def_ErrAmpOV_SizeDecides
import Definitions.Def_ErrAmpOV_ZPDecides
import Definitions.Def_ErrAmpOV_OV
import Definitions.Def_ErrAmpOV_LowDim

set_option autoImplicit false

namespace ErrAmpOV

/-- Theorem 3.1 (Efficient derandomization of zero-error probabilistic circuits for
low-dimensional OV), p.9; formal version of Theorem 1.1, p.2. Let `0 < α < 1` and `c ∈ ℕ`.
Suppose that for every dimension function `d` with `ω(log n) ≤ d(n) ≤ n^{o(1)}`, for all
sufficiently large `n`, `OV_{n,d(n)}` has zero-error probabilistic circuits of size at most
`n^{2−α}·d(n)^c` with error at most `1/10`. Then for every such `d`, for all sufficiently large
`n`, `OV_{n,d(n)}` has deterministic circuits of size at most `n^{2−α/4}·d(n)^c`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Theorem 3.1, p.9 (proof p.11).

**Formalization Note.**
* "For all sufficiently large `n` and all `d := d(n)` between `ω(log n)` and `n^{o(1)}`" is
  `∀ d, LowDim d → ∀ᶠ n in atTop, …`, in the hypothesis and in the conclusion; the threshold
  may depend on `d`.
* `ZPSIZE_{1/10}[S]` and `SIZE[S]` have no `O(·)` on the page: sizes are exact on both sides.
* `α` and `c` are the same in hypothesis and conclusion. `n^{2−α}` and `n^{2−α/4}` are
  `Real.rpow`; `d(n)^c` is a natural power.
* Circuits are `ErrAmpOV.Circuit` (fan-in ≤ 2, size = number of gates); the deterministic
  circuit computes `OV_{n,d(n)}` on every input. -/
theorem theorem_3_1 (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) (c : ℕ)
    (h : ∀ d : ℕ → ℕ, LowDim d → ∀ᶠ n : ℕ in Filter.atTop,
      ZPDecides (1 / 10) ((n : ℝ) ^ (2 - α) * (d n : ℝ) ^ c) (OV n (d n))) :
    ∀ d : ℕ → ℕ, LowDim d → ∀ᶠ n : ℕ in Filter.atTop,
      SizeDecides ((n : ℝ) ^ (2 - α / 4) * (d n : ℝ) ^ c) (OV n (d n)) := by sorry

end ErrAmpOV
