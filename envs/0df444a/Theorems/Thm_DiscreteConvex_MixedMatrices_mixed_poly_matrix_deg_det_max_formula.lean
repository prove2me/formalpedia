-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_mixed_poly_matrix_deg_det_max_formula
-- name    : DiscreteConvex.MixedMatrices.mixed_poly_matrix_deg_det_max_formula
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T06:48:17.061708+00:00
-- url     : https://prove2.me/theorems/166f6385-480e-4a7e-abc9-95cacec57bed
-- title:
--   Theorem 12.13 -- degree of the determinant of a mixed polynomial matrix
-- statement:
--   **Theorem 12.13** (p.360, Eq. (12.14)). For a square mixed polynomial matrix $A(s) = Q(s) + T(s)$,
--   $$\deg\det A = \max\{\deg\det Q[I,J] + \deg\det T[R\setminus I, C\setminus J] \mid |I|=|J|,\ I \subseteq R,\ J \subseteq C\},$$
--   where both sides equal $-\infty$ if $A$ is singular (i.e. $\det A(s)$ is the zero polynomial).
--
--   The polynomial-matrix analogue of Theorem 12.7's rank max-formula: it lets the *degree* of the determinant of a mixed polynomial matrix (relevant to the pole/zero structure of a linear time-invariant system's transfer function) be computed from the numeric parts $Q[I,J]$ and the free-parameter parts $T[R\setminus I, C\setminus J]$ separately, each far cheaper than expanding the full symbolic determinant.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.360, Theorem 12.13.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.360, Theorem 12.13

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedPolyMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_SubDegDet

namespace DiscreteConvex.MixedMatrices

/-- Theorem 12.13 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.360), Eq. (12.14). For a
square mixed polynomial matrix `A(s) = Q(s) + T(s)`,
`deg det A = max{deg det Q[I,J] + deg det T[R\I,C\J] | |I| = |J|, I ⊆ R, J ⊆ C}`, where both sides
are `−∞` if `A` is singular (i.e. `det A(s)` is the zero polynomial; `Polynomial.degree`'s `⊥`
realizes `−∞` throughout). -/
theorem mixed_poly_matrix_deg_det_max_formula {R K F : Type*} [Fintype R] [Field K] [Field F]
    [Algebra K F] [DecidableEq R]
    (A : Matrix R R (Polynomial F)) (Q : Matrix R R (Polynomial K)) (T : Matrix R R (Polynomial F))
    (hA : IsMixedPolyMatrix A Q T) :
    (Matrix.det A).degree =
      ((Finset.univ : Finset (Finset R × Finset R)).filter
          (fun p => p.1.card = p.2.card)).sup
        (fun p => SubDegDet Q p.1 p.2 + SubDegDet T p.1ᶜ p.2ᶜ) := by sorry

end DiscreteConvex.MixedMatrices
