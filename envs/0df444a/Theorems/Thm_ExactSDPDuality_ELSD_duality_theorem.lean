-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_duality_theorem
-- name    : ExactSDPDuality.ELSD.duality_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:20:42.910553+00:00
-- url     : https://prove2.me/theorems/d2c9489c-2240-4ca0-a8f6-a86ba9fc13d4
-- title:
--   Theorem 6 (Duality Theorem) — ELSD: weak duality, zero gap and dual attainment for every SDP
-- statement:
--   Let $Q_0, Q_1,\dots,Q_m$ be real symmetric $n\times n$ matrices, $c\in\mathbb R^m$, and consider the primal semidefinite program
--   $$(\mathrm P)\qquad \sup\ c^{\mathsf T}x\quad\text{s.t.}\quad \sum_{i=1}^m x_iQ_i\preceq Q_0,$$
--   with feasible region $G$. Let (ELSD) be $\inf\,(U+W)\bullet Q_0$ subject to $Q^*(U+W) = c$, $W\in\mathcal W_m$, $U\succeq 0$, and (Weak-ELSD) the same program with $\mathcal W_{m-1}$ in place of $\mathcal W_m$. No constraint qualification is assumed. Then:
--
--   1. (Weak duality) If $x$ is primal feasible and $(U,W)$ is dual feasible (or weakly dual feasible), then $c^{\mathsf T}x\le (U+W)\bullet Q_0$.
--   2. (Primal boundedness) If the primal is feasible, then its optimal value is finite if and only if (ELSD) is feasible, and if and only if (Weak-ELSD) is feasible.
--   3. (Zero gap) If the primal and (ELSD) (or (Weak-ELSD)) are both feasible, then the optimal values of (P), (ELSD) and (Weak-ELSD) are equal: there is a real $v$ that is the supremum of the primal objective values and the infimum of the objective values of both duals.
--   4. (Dual attainment) Whenever the common optimal value of the primal and (ELSD) is finite, i.e. the primal is feasible and bounded above, (ELSD) has a feasible pair $(U,W)$ with $(U+W)\bullet Q_0$ equal to it.
--
--   This is the semidefinite analogue of the linear programming duality theorem, obtained without Slater's condition: the standard Lagrangian dual of (P) can have a positive duality gap or fail to attain, whereas (ELSD), which has polynomial size in the data, never does.
--
--   **Formalization Note** Optimal values are expressed by least upper and greatest lower bounds of the sets of objective values, never by real `sSup`/`sInf`. "Finite optimal value" of a feasible primal is boundedness above of its objective values. In part 3 the hypothesis "(ELSD) or (Weak-ELSD) is feasible" is stated as a disjunction, which covers both readings of the page. For $m = 0$, $\mathcal W_{m-1} = \mathcal W_0 = \{0\}$.
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 138, Theorem 6 (Duality Theorem); proof in §2.3 (pp. 140–141) and §2.5 (pp. 150–153)

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Theorem 6, the Duality Theorem (Ramana 1997, p. 138), for the primal SDP
`sup cᵀx s.t. ∑ᵢ xᵢ Qᵢ ⪯ Q₀` with real symmetric data and no constraint qualification:
(i) weak duality for (ELSD) and (Weak-ELSD);
(ii) a feasible primal has finite optimal value iff (ELSD) (resp. (Weak-ELSD)) is feasible;
(iii) if the primal and (ELSD) (or (Weak-ELSD)) are feasible, the three optimal values coincide;
(iv) when the common optimal value is finite, (ELSD) attains it. -/
theorem duality_theorem {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) :
    -- (i) weak duality
    ((∀ x ∈ feasibleSet Q0 Q, ∀ U W : Matrix (Fin n) (Fin n) ℝ,
        ELSDFeasible Q0 Q c U W → c ⬝ᵥ x ≤ frob (U + W) Q0) ∧
      (∀ x ∈ feasibleSet Q0 Q, ∀ U W : Matrix (Fin n) (Fin n) ℝ,
        WeakELSDFeasible Q0 Q c U W → c ⬝ᵥ x ≤ frob (U + W) Q0)) ∧
    -- (ii) primal boundedness
    ((feasibleSet Q0 Q).Nonempty →
      (BddAbove (primalValues Q0 Q c) ↔ ∃ U W, ELSDFeasible Q0 Q c U W) ∧
        (BddAbove (primalValues Q0 Q c) ↔ ∃ U W, WeakELSDFeasible Q0 Q c U W)) ∧
    -- (iii) zero gap
    ((feasibleSet Q0 Q).Nonempty →
      ((∃ U W, ELSDFeasible Q0 Q c U W) ∨ (∃ U W, WeakELSDFeasible Q0 Q c U W)) →
      ∃ v : ℝ, IsLUB (primalValues Q0 Q c) v ∧ IsGLB (elsdValues Q0 Q c) v ∧
        IsGLB (weakElsdValues Q0 Q c) v) ∧
    -- (iv) dual attainment
    ((feasibleSet Q0 Q).Nonempty → BddAbove (primalValues Q0 Q c) →
      ∃ v : ℝ, IsLUB (primalValues Q0 Q c) v ∧
        ∃ U W, ELSDFeasible Q0 Q c U W ∧ frob (U + W) Q0 = v) := by sorry

end ExactSDPDuality.ELSD
