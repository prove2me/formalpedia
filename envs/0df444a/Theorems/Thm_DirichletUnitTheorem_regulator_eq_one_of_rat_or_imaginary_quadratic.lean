-- Prove2me | Theorems.Thm_DirichletUnitTheorem_regulator_eq_one_of_rat_or_imaginary_quadratic
-- name    : DirichletUnitTheorem.regulator_eq_one_of_rat_or_imaginary_quadratic
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:37.110906+00:00
-- url     : https://prove2.me/theorems/7dfac2d2-43b8-42fa-9eb0-e52c86e353fb
-- title:
--   The regulator of $\mathbb Q$ and of imaginary quadratic fields is $1$
-- statement:
--   If $K=\mathbb Q$ or $K$ is an imaginary quadratic field, then the regulator of $K$ equals $1$ (the determinant of a $0\times 0$ matrix):
--
--   $$\operatorname{Reg}(K)=1.$$
--
--   **Formalization Note** The regulator is Mathlib's `NumberField.Units.regulator`; "$K=\mathbb Q$" is encoded as $[K:\mathbb Q]=1$ and "imaginary quadratic" as degree $2$ and `IsTotallyComplex`.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), section "The regulator", Examples, first bullet.

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem regulator_eq_one_of_rat_or_imaginary_quadratic (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 1 ∨ (Module.finrank ℚ K = 2 ∧ IsTotallyComplex K)) :
    Units.regulator K = 1 := by sorry

end DirichletUnitTheorem
