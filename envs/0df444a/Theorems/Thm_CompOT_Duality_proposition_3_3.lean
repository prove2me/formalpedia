-- Prove2me | Theorems.Thm_CompOT_Duality_proposition_3_3
-- name    : CompOT.Duality.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:34.187094+00:00
-- url     : https://prove2.me/theorems/88e15ac1-56f5-4d7e-b3ca-2970352a02fb
-- title:
--   Proposition 3.3, p. 405 — complementary feasible P and (f, g) are primal and dual optimal
-- statement:
--   Let $a \in \Sigma_n$, $b \in \Sigma_m$ be histograms and $C \in \mathbb R^{n\times m}$. Suppose $P \in \mathbf U(a,b)$ is primal feasible, $(f,g) \in \mathbf R(C)$ is dual feasible, and $P$ and $(f,g)$ are complementary w.r.t. $C$ (Definition 3.1: $C_{i,j} = f_i + g_j$ whenever $P_{i,j} > 0$). Then
--
--   1. $P$ is optimal for the primal problem: $\langle C,P\rangle \le \langle C,Q\rangle$ for all $Q \in \mathbf U(a,b)$;
--   2. $(f,g)$ is optimal for the dual problem: $\langle f',a\rangle + \langle g',b\rangle \le \langle f,a\rangle + \langle g,b\rangle$ for all $(f',g') \in \mathbf R(C)$.
--
--   This is the sufficiency half of complementary slackness: complementarity certifies optimality of both solutions at once.
--
--   **Formalization Note** The page cites the primal and dual as "(2.24)" and "(2.11)"; these are the measure-theoretic problem and the discrete primal. The intended problems are the discrete primal (2.11) and dual (2.20), which is what is stated here.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 3.3 and Definition 3.1, p. 405

import Mathlib
import Definitions.Def_CompOT_Duality_Defs

namespace CompOT.Duality

/-- Proposition 3.3, p. 405: if `P ∈ U(a, b)` and `(f, g) ∈ R(C)` are complementary
(Definition 3.1), then `P` is optimal for the primal (2.11) and `(f, g)` is optimal for the
dual (2.20). -/
theorem proposition_3_3 {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C P : Matrix (Fin n) (Fin m) ℝ) (hP : P ∈ CompOT.Assignment.couplings a b)
    (f : Fin n → ℝ) (g : Fin m → ℝ) (hfg : dualFeasible C f g)
    (hcomp : Complementary C P f g) :
    CompOT.Assignment.IsOptimalCoupling C a b P ∧ IsDualOptimal C a b f g := by sorry

end CompOT.Duality
