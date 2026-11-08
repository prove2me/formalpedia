-- Prove2me | Theorems.Thm_ErrAmpOV_lemma_2_4
-- name    : ErrAmpOV.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:35.039179+00:00
-- url     : https://prove2.me/theorems/7535c6ec-ad03-4bec-9df8-1902119af9a1
-- title:
--   Lemma 2.4 — selector circuits of linear size
-- statement:
--   There is a constant $C>0$ and, for every $n$, a circuit $\mathsf{SEL}_n$ with at most $Cn$ gates such that for all $x,y\in\{0,1\}^n$ and $b\in\{0,1\}$,
--   $$
--   \mathsf{SEL}_n(x,y;b)=\begin{cases}x & b=0,\\ y & b=1.\end{cases}
--   $$
--
--   The selector is how the amplified circuit replaces its output by $\bot$ and how it chooses between the two halves of a compacted list.
--
--   Differences from the source:
--   - reading: a family of size O(n) → ∃ C > 0, ∀ n, size ≤ C·n; reason: the standard meaning of O(n) on a family; at n = 0 no gate is needed, so the bound holds for every n
--   - encoding: Boolean circuits, no gate basis fixed, size = number of gates → ErrAmpOV.Circuit: constant, NOT, AND, OR gates of fan-in at most 2, unbounded fan-out, inputs not counted, a list of output wires; a read of a gate not yet computed returns false; reason: the basis is unspecified on the page; complete fan-in-2 bases differ by a constant factor, and the out-of-range read only gives a free constant false
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Lemma 2.4, p.8

import Mathlib
import Definitions.Def_ErrAmpOV_Circuit

set_option autoImplicit false

namespace ErrAmpOV

/-- Lemma 2.4 (Selector circuits), p.8. There is a constant `C > 0` and, for every `n`, a circuit
`SEL_n` with at most `C·n` gates, reading `x, y ∈ {0,1}^n` and a bit `b`, whose `n` outputs are
`x` if `b = 0` and `y` if `b = 1`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Lemma 2.4, p.8.

**Formalization Note.** "Size `O(n)`" is `∃ C > 0, ∀ n, size ≤ C·n`. The inputs are indexed by
`(Fin n ⊕ Fin n) ⊕ Unit`: `x` on the left copy, `y` on the right copy, `b` on `Unit`. -/
theorem lemma_2_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ SEL : Circuit ((Fin n ⊕ Fin n) ⊕ Unit),
      (SEL.size : ℝ) ≤ C * n ∧
      ∀ (x y : Fin n → Bool) (b : Bool),
        SEL.eval (Sum.elim (Sum.elim x y) (fun _ => b)) = List.ofFn (fun i => if b then y i else x i) := by sorry

end ErrAmpOV
