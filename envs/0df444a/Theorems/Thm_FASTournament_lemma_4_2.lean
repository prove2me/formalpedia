-- Prove2me | Theorems.Thm_FASTournament_lemma_4_2
-- name    : FASTournament.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:25.481012+00:00
-- url     : https://prove2.me/theorems/d12bbc33-0e70-43e4-ab2a-44dc4f438e01
-- title:
--   Lemma 4.2 — a $\{0,1\}$-test for total dual integrality of $Ax\ge b,\ x\ge 0$
-- statement:
--   Let $A$ be a nonnegative integral $m\times n$ matrix with no zero row, and let $b\in\mathbb Q^m$. Then the system $Ax\ge b,\ x\ge 0$ is TDI if and only if for each $\{0,1\}$-vector $y\in\{0,1\}^m$ there exists an integral vector $z\ge 0$ with
--   $$
--   z^TA\le\Big\lceil\frac{y^TA}{2}\Big\rceil\qquad\text{and}\qquad 2z^Tb\ge y^Tb,
--   $$
--   the ceiling taken componentwise.
--
--   The paper adapts this from Schrijver's Corollary 22.13d (stated there for $Ax\le b$); it reduces total dual integrality to finitely many integer programs and underlies the computer-assisted proof of Lemma 4.1.
--
--   Differences from the source:
--   - encoding: an m × n nonnegative integral matrix A, {0, 1}-vectors y, ⌈yᵀA/2⌉ → A : Matrix (Fin m) (Fin n) ℤ with entries ≥ 0; y : Fin m → ℤ with entries in {0, 1}; the ceiling componentwise in ℚ; reason: the same objects
--   - encoding: TDI: for every nonnegative integral w for which the optimum is finite, the dual maximum has an integral optimal solution → IsTDI: for every integral w for which the real primal LP is feasible and bounded below, some integral dual-feasible y has objective at least that of every real dual-feasible vector; reason: for the nonnegative incidence matrices a cost with a negative entry makes the primal infeasible or unbounded, and by LP duality a finite primal optimum means an attained dual maximum; same notion
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 4.2, p.23

import Mathlib
import Definitions.Def_FASTournament_IsTDI

namespace FASTournament

/-- **Lemma 4.2.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 4.2, p.23: "Let A be a nonnegative integral matrix with no zero row, and let b be a
rational vector. Then the system Ax ≥ b, x ≥ 0 is TDI iff for each {0, 1}-vector y, there exists
an integral vector z ≥ 0 with zTA ≤ ⌈yTA/2⌉ and 2zTb ≥ yTb."

**Formalization Note.** `A` is `m × n` with entries in `ℤ`; `y` and `z` are row vectors indexed
by the rows; `⌈yᵀA/2⌉` is taken componentwise. -/
theorem lemma_4_2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, A i j ≠ 0) :
    IsTDI A b ↔
      ∀ y : Fin m → ℤ, (∀ i, y i = 0 ∨ y i = 1) →
        ∃ z : Fin m → ℤ, (∀ i, 0 ≤ z i) ∧
          (∀ j, ∑ i, z i * A i j ≤ ⌈((∑ i, y i * A i j : ℤ) : ℚ) / 2⌉) ∧
          ∑ i, (y i : ℚ) * b i ≤ 2 * ∑ i, (z i : ℚ) * b i := by sorry

end FASTournament
