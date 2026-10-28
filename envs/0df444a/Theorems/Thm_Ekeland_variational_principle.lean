-- Prove2me | Theorems.Thm_Ekeland_variational_principle
-- name    : Ekeland.variational_principle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:30.328331+00:00
-- url     : https://prove2.me/theorems/b93134ec-0a2b-4046-9d69-2defd6b00691
-- title:
--   Ekeland’s variational principle
-- statement:
--   **Ekeland's variational principle.** Let $(X, d)$ be a complete metric space and let
--   $H : X \to \mathbb{R}$ be lower semicontinuous and bounded below, say $H \ge m$ for a constant
--   $m$. Fix $\delta > 0$ and an arbitrary starting point $x_1 \in X$. Then there exists a point
--   $x \in X$ with
--
--   $$
--   H(x) \;\le\; H(x_1) \qquad\text{and}\qquad H(x) \;\le\; H(y) + \delta\, d(y, x) \quad \text{for every } y \in X .
--   $$
--
--   The second inequality says that $x$ is an exact global minimizer of the perturbed function
--   $y \mapsto H(y) + \delta\, d(y, x)$, while the first says that passing to $x$ did not increase
--   the value of $H$. So a function that is merely bounded below, with no compactness and no
--   attained minimum, always has points that are minima after an arbitrarily small Lipschitz
--   perturbation.
--
--   This is one of the basic tools of nonlinear analysis: it replaces compactness arguments in
--   proofs of surjectivity, of the existence of critical points, and of maximal monotonicity of
--   subdifferentials, where the perturbation parameter $\delta$ is taken small at the end.
-- source:
--   I. Ekeland, On the variational principle, J. Math. Anal. Appl. 47 (1974), 324–353, Theorem 1.1; carved from the accepted proof of RockafellarMaxMono.Cyclic.maximal_cyclically_monotone_iff_subdiff, https://prove2.me/submissions/23d86335-ed0d-406b-b7dd-748579bde0b9

import Mathlib

set_option autoImplicit false

theorem Ekeland.variational_principle {X : Type*} [MetricSpace X] [CompleteSpace X] (H : X → ℝ)
    (hH : LowerSemicontinuous H) (m : ℝ) (hm : ∀ x, m ≤ H x) (δ : ℝ) (hδ : 0 < δ) (x₁ : X) :
    ∃ x, H x ≤ H x₁ ∧ ∀ y, H x ≤ H y + δ * dist y x := by sorry
