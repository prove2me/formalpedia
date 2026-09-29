-- Prove2me | Theorems.Thm_DoCarmoDG_fundamental_theorem_local_theory_of_curves
-- name    : DoCarmoDG.fundamental_theorem_local_theory_of_curves
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T00:55:38.058198+00:00
-- url     : https://prove2.me/theorems/4cd095fa-4be3-4cea-b45e-470bee4d7378
-- title:
--   Fundamental theorem of the local theory of curves
-- statement:
--   **Fundamental theorem of the local theory of curves** (do Carmo, p. 19).
--
--   Given differentiable functions $k(s) > 0$ and $\tau(s)$, $s \in I$, there exists a regular parametrized curve $\alpha : I \to \mathbb{R}^3$ such that $s$ is the arc length, $k(s)$ is the curvature, and $\tau(s)$ is the torsion of $\alpha$. Moreover, any other curve $\bar\alpha$ satisfying the same conditions differs from $\alpha$ by a rigid motion; that is, there exist an orthogonal linear map $\rho$ of $\mathbb{R}^3$ with positive determinant and a vector $c$ such that $\bar\alpha = \rho \circ \alpha + c$.
--
--   Here $I = (a,b)$ is an open interval, curvature and torsion are those of do Carmo §1-5, and the torsion uses his sign convention $b' = \tau n$.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-5 (pp. 17-22)

import Definitions.Def_DoCarmo_local_theory_curves

namespace DoCarmoDG

theorem fundamental_theorem_local_theory_of_curves
    (a b : ℝ) (k tau : ℝ → ℝ)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) k (Set.Ioo a b))
    (htau : ContDiffOn ℝ (⊤ : ℕ∞) tau (Set.Ioo a b))
    (hkpos : ∀ s ∈ Set.Ioo a b, 0 < k s) :
    (∃ alpha : ℝ → EuclideanSpace ℝ (Fin 3),
        IsArcLengthCurve (Set.Ioo a b) alpha ∧
        (∀ s ∈ Set.Ioo a b, curvature alpha s = k s) ∧
        (∀ s ∈ Set.Ioo a b, torsion alpha s = tau s)) ∧
      (∀ alpha beta : ℝ → EuclideanSpace ℝ (Fin 3),
        IsArcLengthCurve (Set.Ioo a b) alpha →
        IsArcLengthCurve (Set.Ioo a b) beta →
        (∀ s ∈ Set.Ioo a b, curvature alpha s = k s ∧ torsion alpha s = tau s) →
        (∀ s ∈ Set.Ioo a b, curvature beta s = k s ∧ torsion beta s = tau s) →
        ∃ M : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
          IsRigidMotion M ∧ ∀ s ∈ Set.Ioo a b, beta s = M (alpha s)) := by sorry

end DoCarmoDG
