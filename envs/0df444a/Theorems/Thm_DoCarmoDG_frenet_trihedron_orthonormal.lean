-- Prove2me | Theorems.Thm_DoCarmoDG_frenet_trihedron_orthonormal
-- name    : DoCarmoDG.frenet_trihedron_orthonormal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T00:19:55.013872+00:00
-- url     : https://prove2.me/theorems/47e67018-ecbd-43de-901c-a9e11a9574ba
-- title:
--   The Frenet trihedron $\{t,n,b\}$ is orthonormal
-- statement:
--   For a curve $\alpha$ parametrized by arc length on an open interval $(a,b)$ whose curvature does not vanish, the tangent $t(s)$, normal $n(s)$ and binormal $b(s)$ form an orthonormal triple at every $s \in (a,b)$: each has unit length and they are pairwise orthogonal. This is the assertion, made in the text of do Carmo §1-5, that "to each value of the parameter $s$ we have associated three orthogonal unit vectors $t(s), n(s), b(s)$".
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-5 (pp. 17-22)

import Definitions.Def_DoCarmo_local_theory_curves

namespace DoCarmoDG

theorem frenet_trihedron_orthonormal
    (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) :
    ∀ s ∈ Set.Ioo a b,
      ‖tangent alpha s‖ = 1 ∧ ‖normal alpha s‖ = 1 ∧ ‖binormal alpha s‖ = 1 ∧
      inner ℝ (tangent alpha s) (normal alpha s) = 0 ∧
      inner ℝ (normal alpha s) (binormal alpha s) = 0 ∧
      inner ℝ (binormal alpha s) (tangent alpha s) = 0 := by sorry

end DoCarmoDG
