-- Prove2me | Theorems.Thm_CompOT_DualAscent_proposition_3_3
-- name    : CompOT.DualAscent.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:19.883986+00:00
-- url     : https://prove2.me/theorems/8c02b617-adbe-4dd1-ab17-521f49d8f015
-- title:
--   Proposition 3.3, p. 405 — a complementary pair of feasible primal and dual solutions is primal and dual optimal
-- statement:
--   Let $C \in \mathbb{R}^{n\times m}$, $a \in \mathbb{R}^n$, $b \in \mathbb{R}^m$. Suppose $P \in U(a,b)$ is a feasible coupling, $(f,g) \in R(C)$ is a feasible pair of dual potentials ($f_i + g_j \le C_{i,j}$ for all $i, j$), and $P$ and $(f,g)$ are complementary: $P_{i,j} > 0$ implies $C_{i,j} = f_i + g_j$. Then
--   $$\langle C, P\rangle \le \langle C, Q\rangle \ \ \forall Q \in U(a,b) \qquad\text{and}\qquad \langle f', a\rangle + \langle g', b\rangle \le \langle f, a\rangle + \langle g, b\rangle\ \ \forall (f',g') \in R(C),$$
--   that is, $P$ is optimal for the primal problem (2.11) and $(f,g)$ is optimal for the dual problem (3.4).
--
--   This is the certificate of optimality used throughout chapter 3: in the dual ascent method it is what shows that a dual pair admitting a complementary feasible coupling cannot be improved.
--
--   **Formalization Note** The page refers to the primal and dual as "(2.24)" and "(2.11)"; the intended problems are (2.11) (primal) and (2.20)/(3.4) (dual), which is what the Lean states. No assumption on $a, b$ is needed: the existence of $P \in U(a,b)$ already forces $a, b \ge 0$ with equal total mass. Indices are 0-based (`Fin n`, `Fin m`).
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 3.3, p. 405

import Mathlib
import Definitions.Def_CompOT_DualAscent_Defs

namespace CompOT.DualAscent

/-- Proposition 3.3, p. 405: a feasible coupling `P ∈ U(a, b)` and a dual feasible pair
`(f, g) ∈ R(C)` that are complementary (Definition 3.1) are primal and dual optimal. -/
theorem proposition_3_3 {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hP : P ∈ CompOT.Assignment.couplings a b) (hfg : CompOT.Duality.dualFeasible C f g) (hcomp : CompOT.Duality.Complementary C P f g) :
    CompOT.Assignment.IsOptimalCoupling C a b P ∧ CompOT.Duality.IsDualOptimal C a b f g := by sorry

end CompOT.DualAscent
