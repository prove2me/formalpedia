-- Prove2me | Theorems.Thm_FASTournament_lemma_4_3
-- name    : FASTournament.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:20.37697+00:00
-- url     : https://prove2.me/theorems/a6896504-a34f-4905-a42d-5fbe23097ecf
-- title:
--   Lemma 4.3 — the $\{0,1\}$-test restricted by lexicographic domination
-- statement:
--   Let $A$ be a nonnegative integral $m\times n$ matrix with no zero row. For $\{0,1\}$-vectors $u,v\in\{0,1\}^m$ write $u\prec v$ if there is an index $j$ with $u_i=v_i$ for all $i<j$ and $u_j<v_j$ (lexicographic order). Let $\mathcal V$ and $\mathcal W$ be two sets of $\{0,1\}$-vectors such that for each $v\in\mathcal V$ there exists $w\in\mathcal W$ with
--   $$
--   v\prec w,\qquad v^T\mathbf 1=w^T\mathbf 1,\qquad w^TA\le v^TA.
--   $$
--   Let $\mathcal U$ consist of all $\{0,1\}$-vectors $u$ such that $u^T\mathbf 1$ is odd and $u\not\ge v$ for each $v\in\mathcal V$. Then the system $Ax\ge\mathbf 1,\ x\ge 0$ is TDI if and only if for each $y\in\mathcal U$ there exists an integral vector $z\ge 0$ with
--   $$
--   z^TA\le\Big\lceil\frac{y^TA}{2}\Big\rceil\qquad\text{and}\qquad 2z^T\mathbf 1\ge y^T\mathbf 1.
--   $$
--
--   This refinement of Lemma 4.2 cuts the $2^{41}$ cases for $G_1$ down to the 41022 odd stable sets of Claim 3.
--
--   **Formalization Note** $u\not\ge v$ is the negation of the componentwise order $v\le u$; the order $\prec$ follows the row order of $A$.
--
--   Differences from the source:
--   - encoding: an m × n nonnegative integral matrix A, {0, 1}-vectors y, ⌈yᵀA/2⌉ → A : Matrix (Fin m) (Fin n) ℤ with entries ≥ 0; y : Fin m → ℤ with entries in {0, 1}; the ceiling componentwise in ℚ; reason: the same objects
--   - encoding: TDI: for every nonnegative integral w for which the optimum is finite, the dual maximum has an integral optimal solution → IsTDI: for every integral w for which the real primal LP is feasible and bounded below, some integral dual-feasible y has objective at least that of every real dual-feasible vector; reason: for the nonnegative incidence matrices a cost with a negative entry makes the primal infeasible or unbounded, and by LP duality a finite primal optimum means an attained dual maximum; same notion
--   - encoding: sets V, W of {0,1}-vectors and the order ≺ → Vs, Ws : Set (Fin m → ℤ) with 0/1 entries; v ≺ w as ∃ j, (∀ i < j, v i = w i) ∧ v j < w j; reason: the same objects, with rows indexed by Fin m
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 4.3, p.24

import Mathlib
import Definitions.Def_FASTournament_IsTDI

namespace FASTournament

/-- **Lemma 4.3.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 4.3, p.24: "Let A be a nonnegative integral matrix with no zero row. Let V and W be
two sets of {0, 1}-vectors such that for each v ∈ V, there exists w ∈ W satisfying v ≺ w,
vT1 = wT1, and wTA ≤ vTA. Let U consist of all {0, 1}-vectors u such that uT1 is odd and u ≱ v
for each v ∈ V. Then the system Ax ≥ 1, x ≥ 0 is TDI iff for each y ∈ U, there exists an
integral vector z ≥ 0 with zTA ≤ ⌈yTA/2⌉ and 2zT1 ≥ yT1."
Here (p.24) `u ≺ v` "if there exists a subscript j, with 1 ≤ j ≤ m, such that ui = vi for all
1 ≤ i < j and uj < vj".

**Formalization Note.** `A` is `m × n` over `ℤ`; the sets `V`, `W` are `Vs`, `Ws`; `≺` is the
strict lexicographic order in the row order `Fin m`; `u ≱ v` is `¬ v ≤ u` componentwise; the
membership `y ∈ U` is spelled out in the hypotheses of the right-hand side. -/
theorem lemma_4_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, A i j ≠ 0) (Vs Ws : Set (Fin m → ℤ))
    (hV : ∀ v ∈ Vs, ∀ i, v i = 0 ∨ v i = 1) (hW : ∀ w ∈ Ws, ∀ i, w i = 0 ∨ w i = 1)
    (hVW : ∀ v ∈ Vs, ∃ w ∈ Ws, (∃ j : Fin m, (∀ i < j, v i = w i) ∧ v j < w j) ∧
      ∑ i, v i = ∑ i, w i ∧ ∀ k, ∑ i, w i * A i k ≤ ∑ i, v i * A i k) :
    IsTDI A (fun _ => 1) ↔
      ∀ y : Fin m → ℤ, (∀ i, y i = 0 ∨ y i = 1) → Odd (∑ i, y i) → (∀ v ∈ Vs, ¬ v ≤ y) →
        ∃ z : Fin m → ℤ, (∀ i, 0 ≤ z i) ∧
          (∀ j, ∑ i, z i * A i j ≤ ⌈((∑ i, y i * A i j : ℤ) : ℚ) / 2⌉) ∧
          ∑ i, y i ≤ 2 * ∑ i, z i := by sorry

end FASTournament
