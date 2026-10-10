-- Prove2me | Theorems.Thm_DirichletUnitTheorem_regulator_cyclic_cubic_approx
-- name    : DirichletUnitTheorem.regulator_cyclic_cubic_approx
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:36:00.360926+00:00
-- url     : https://prove2.me/theorems/e10c7db1-cfd4-45d0-9b29-cc39670e5b3d
-- title:
--   The regulator of the cyclic cubic field of discriminant $49$ is $\approx 0.5255$
-- statement:
--   Let $K$ be a number field with $[K:\mathbb Q]=3$ containing an element $\alpha$ with $\alpha^3+\alpha^2-2\alpha-1=0$ (so $K=\mathbb Q(\alpha)$ is the cyclic cubic field of discriminant $49$). Then its regulator satisfies
--
--   $$0.5254<\operatorname{Reg}(K)<0.5256,$$
--
--   consistent with the value $\operatorname{Reg}(K)\approx0.525455$.
--
--   **Formalization Note** The source gives only an approximate value; it is encoded as the interval $(0.5254, 0.5256)$. The regulator is Mathlib's `NumberField.Units.regulator`.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), section "The regulator", Examples, third bullet and figure caption ("approximately 0.5255", "approximately 0.525455").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem regulator_cyclic_cubic_approx (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) (α : K) (hα : α ^ 3 + α ^ 2 - 2 * α - 1 = 0) :
    0.5254 < Units.regulator K ∧ Units.regulator K < 0.5256 := by sorry

end DirichletUnitTheorem
