-- Prove2me | Theorems.Thm_DirichletUnitTheorem_regulator_golden_field
-- name    : DirichletUnitTheorem.regulator_golden_field
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:58.956988+00:00
-- url     : https://prove2.me/theorems/008894fb-fc50-45d9-bf15-7849d6284dd1
-- title:
--   The regulator of $\mathbb Q(\sqrt5)$ is $\log\frac{1+\sqrt5}{2}$
-- statement:
--   Let $K=\mathbb Q(\sqrt5)$ be the golden field. Its regulator is the logarithm of the golden ratio, its fundamental unit:
--
--   $$\operatorname{Reg}\big(\mathbb Q(\sqrt5)\big)=\log\frac{1+\sqrt5}{2}.$$
--
--   **Formalization Note** The golden field is characterized as a number field $K$ of degree $2$ containing an element $\alpha$ with $\alpha^2=\alpha+1$ (such an $\alpha$ generates $K$, so $K\cong\mathbb Q(\sqrt5)$). The regulator is Mathlib's `NumberField.Units.regulator`.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), section "The regulator", Examples, second bullet (golden field).

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem regulator_golden_field (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (α : K) (hα : α ^ 2 = α + 1) :
    Units.regulator K = Real.log ((1 + Real.sqrt 5) / 2) := by sorry

end DirichletUnitTheorem
