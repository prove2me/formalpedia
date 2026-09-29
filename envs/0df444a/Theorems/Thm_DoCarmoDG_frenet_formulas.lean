-- Prove2me | Theorems.Thm_DoCarmoDG_frenet_formulas
-- name    : DoCarmoDG.frenet_formulas
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T00:26:51.690241+00:00
-- url     : https://prove2.me/theorems/cc5ddf1e-00ca-4974-8077-2fcf60255edb
-- title:
--   Frenet formulas: $t' = kn$, $n' = -kt - \tau b$, $b' = \tau n$
-- statement:
--   The Frenet formulas of do Carmo §1-5. For a curve parametrized by arc length with nowhere vanishing curvature, the three vector fields of the Frenet trihedron are differentiable and satisfy
--
--   $$ t' = k\,n, \qquad n' = -k\,t - \tau\,b, \qquad b' = \tau\,n $$
--
--   at every point of the interval, where $k$ is the curvature and $\tau$ the torsion in do Carmo's sign convention.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-5 (pp. 17-22)

import Definitions.Def_DoCarmo_local_theory_curves

namespace DoCarmoDG

theorem frenet_formulas
    (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) :
    ∀ s ∈ Set.Ioo a b,
      HasDerivAt (tangent alpha) (curvature alpha s • normal alpha s) s ∧
      HasDerivAt (normal alpha)
        (-(curvature alpha s) • tangent alpha s - torsion alpha s • binormal alpha s) s ∧
      HasDerivAt (binormal alpha) (torsion alpha s • normal alpha s) s := by sorry

end DoCarmoDG
