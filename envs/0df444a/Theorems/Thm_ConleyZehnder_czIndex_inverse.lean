-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_inverse
-- name    : ConleyZehnder.czIndex_inverse
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:23:37.521677+00:00
-- url     : https://prove2.me/theorems/e8f63907-d0a5-4b81-8abb-21159e307fb1
-- title:
--   Inverse property of the Conley–Zehnder index
-- statement:
--   For every $\psi\in\mathrm{SP}(n)$,
--   $$\mu_{CZ}(\psi^{-1})=\mu_{CZ}(\psi^{\mathsf T})=-\mu_{CZ}(\psi),$$
--   where $\psi^{-1}$ and $\psi^{\mathsf T}$ are the paths $t\mapsto\psi(t)^{-1}$ and $t\mapsto\psi(t)^{\mathsf T}$.
--
--   **Formalization Note** Both paths are passed as continuous paths with the stated pointwise values.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (8), p. 7; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt, Proposition 8 (8), Inverse: `μ_CZ(ψ⁻¹) = μ_CZ(ψᵀ) = -μ_CZ(ψ)`. -/
theorem czIndex_inverse {n : ℕ} (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n)
    (ψinv ψtr : C(unitInterval, Mat n)) (hinv : ∀ t, ψinv t = (ψ t)⁻¹)
    (htr : ∀ t, ψtr t = (ψ t).transpose) :
    czIndex ψinv = -czIndex ψ ∧ czIndex ψtr = -czIndex ψ := by sorry

end ConleyZehnder
