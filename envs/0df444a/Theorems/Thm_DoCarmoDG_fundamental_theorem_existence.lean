-- Prove2me | Theorems.Thm_DoCarmoDG_fundamental_theorem_existence
-- name    : DoCarmoDG.fundamental_theorem_existence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T00:54:51.225307+00:00
-- url     : https://prove2.me/theorems/b9c47910-5626-4638-a22e-0eec68c0786f
-- title:
--   Existence: every pair $(k > 0, \tau)$ is realized by a curve
-- statement:
--   The existence half of the fundamental theorem of the local theory of curves (do Carmo p. 19; proof deferred to the appendix of Chapter 4). Given smooth functions $k(s) > 0$ and $\tau(s)$ on an interval $I$, there is a curve $\alpha : I \to \mathbb{R}^3$ parametrized by arc length whose curvature is $k$ and whose torsion is $\tau$. The curve is obtained by solving the linear Frenet system for the moving frame and integrating its tangent component.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-5 (pp. 17-22)

import Definitions.Def_DoCarmo_local_theory_curves

namespace DoCarmoDG

theorem fundamental_theorem_existence
    (a b : ℝ) (k tau : ℝ → ℝ)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) k (Set.Ioo a b))
    (htau : ContDiffOn ℝ (⊤ : ℕ∞) tau (Set.Ioo a b))
    (hkpos : ∀ s ∈ Set.Ioo a b, 0 < k s) :
    ∃ alpha : ℝ → EuclideanSpace ℝ (Fin 3),
      IsArcLengthCurve (Set.Ioo a b) alpha ∧
      (∀ s ∈ Set.Ioo a b, curvature alpha s = k s) ∧
      (∀ s ∈ Set.Ioo a b, torsion alpha s = tau s) := by sorry

end DoCarmoDG
