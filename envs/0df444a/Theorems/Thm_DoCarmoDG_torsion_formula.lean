-- Prove2me | Theorems.Thm_DoCarmoDG_torsion_formula
-- name    : DoCarmoDG.torsion_formula
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T00:46:26.904421+00:00
-- url     : https://prove2.me/theorems/9fd7e4b3-0469-48d2-982a-1624e628e731
-- title:
--   $\tau = -(\alpha' \wedge \alpha'') \cdot \alpha''' / k^2$
-- statement:
--   do Carmo §1-5, Exercise 2 (p. 23): for a curve parametrized by arc length with $k(s) \neq 0$, the torsion is given in terms of the first three derivatives by
--
--   $$ \tau(s) = -\,\frac{(\alpha'(s) \wedge \alpha''(s)) \cdot \alpha'''(s)}{k(s)^2} . $$
--
--   The sign is do Carmo's, matching his convention $b' = \tau n$.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-5 (pp. 17-22)

import Definitions.Def_DoCarmo_local_theory_curves

namespace DoCarmoDG

theorem torsion_formula
    (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) :
    ∀ s ∈ Set.Ioo a b,
      torsion alpha s =
        -(inner ℝ (cross (deriv alpha s) (deriv (deriv alpha) s))
            (deriv (deriv (deriv alpha)) s)) / (curvature alpha s) ^ 2 := by sorry

end DoCarmoDG
