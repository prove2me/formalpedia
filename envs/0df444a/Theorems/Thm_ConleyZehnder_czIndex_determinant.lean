-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_determinant
-- name    : ConleyZehnder.czIndex_determinant
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:23:16.830117+00:00
-- url     : https://prove2.me/theorems/af8daa41-b4a6-48dd-8969-991d26e7763e
-- title:
--   Determinant property of the Conley–Zehnder index
-- statement:
--   For every $\psi\in\mathrm{SP}(n)$,
--   $$(-1)^{\,n-\mu_{CZ}(\psi)}=\operatorname{sign}\det\big(\mathrm{Id}-\psi(1)\big).$$
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (7), p. 7; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt, Proposition 8 (7), Determinant:
`(-1)^{n - μ_CZ(ψ)} = sign det(Id - ψ(1))`. -/
theorem czIndex_determinant {n : ℕ} (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) :
    (-1 : ℝ) ^ ((n : ℤ) - czIndex ψ) = Real.sign (1 - ψ 1).det := by sorry

end ConleyZehnder
