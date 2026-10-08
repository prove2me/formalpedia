-- Prove2me | Theorems.Thm_AugLagLLC_Feas_caratheodory_cones
-- name    : AugLagLLC.Feas.caratheodory_cones
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:36:24.701573+00:00
-- url     : https://prove2.me/theorems/b7ad25d5-af32-4b02-9936-31225b8d6c8c
-- title:
--   Carathéodory's theorem of cones ([7, p. 689]), as used for (4.3), p. 7 — a linearly independent sub-representation
-- statement:
--   Let $V$ be a real vector space, let $a_i$ ($i\in\iota$, a finite index set) and $b_j$ ($j\in\kappa$) be vectors of $V$, and let $J_0\subseteq\kappa$ be finite. Suppose
--   $$w=\sum_{i\in\iota}\alpha_i a_i+\sum_{j\in J_0}\beta_j b_j\qquad\text{with }\beta_j\ge0\ (j\in J_0).$$
--   Then there are subsets $I\subseteq\iota$ and $J\subseteq J_0$ and coefficients $\hat\alpha_i$ ($i\in I$) and $\hat\beta_j\ge0$ ($j\in J$) such that
--   $$w=\sum_{i\in I}\hat\alpha_i a_i+\sum_{j\in J}\hat\beta_j b_j$$
--   and the vectors $\{a_i\}_{i\in I}\cup\{b_j\}_{j\in J}$ are linearly independent.
--
--   This is Carathéodory's theorem for cones with additional free (sign-unconstrained) generators. In the proof of Theorem 4.1 it is applied with $a_i=\nabla[h_2(x_k)]_i$, $b_j=\nabla[g_2(x_k)]_j$ and $J_0$ the constraints active at $x_*$, producing (4.3); the proof of Theorem 4.2 uses it the same way.
--
--   **Formalization Note** The statement is the generic form of the paper's application; the paper cites it from Bertsekas, *Nonlinear Programming*, 2nd ed., p. 689. Linear independence is that of the family indexed by the disjoint union $I\oplus J$, so a vector appearing twice counts as dependent. Mathlib has only the convex-hull form of Carathéodory's theorem.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, p. 7, proof of Theorem 4.1, the step leading to (4.3), citing Bertsekas, Nonlinear Programming, 2nd ed., Athena Scientific 1999, p. 689 (Carathéodory's theorem for cones)

import Mathlib

namespace AugLagLLC.Feas
theorem caratheodory_cones {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι κ : Type*} [Fintype ι] (a : ι → V) (b : κ → V) (J₀ : Finset κ)
    (α : ι → ℝ) (β : κ → ℝ) (hβ : ∀ j ∈ J₀, 0 ≤ β j) :
    ∃ (I : Finset ι) (J : Finset κ), J ⊆ J₀ ∧
      ∃ (α' : ι → ℝ) (β' : κ → ℝ), (∀ j ∈ J, 0 ≤ β' j) ∧
        ∑ i, α i • a i + ∑ j ∈ J₀, β j • b j = ∑ i ∈ I, α' i • a i + ∑ j ∈ J, β' j • b j ∧
        LinearIndependent ℝ (Sum.elim (fun i : I => a i) (fun j : J => b j)) := by sorry
end AugLagLLC.Feas
