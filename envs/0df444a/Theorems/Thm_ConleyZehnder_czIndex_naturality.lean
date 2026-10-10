-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_naturality
-- name    : ConleyZehnder.czIndex_naturality
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:21:20.124902+00:00
-- url     : https://prove2.me/theorems/4532aba3-02fe-4326-8847-08711fa39fa3
-- title:
--   Naturality of the Conley–Zehnder index
-- statement:
--   Let $\varphi:[0,1]\to\mathrm{Sp}(2n)$ be any continuous path and $\psi\in\mathrm{SP}(n)$. Then
--   $$\mu_{CZ}\big(\varphi\,\psi\,\varphi^{-1}\big)=\mu_{CZ}(\psi),$$
--   where $\varphi\psi\varphi^{-1}$ is the path $t\mapsto\varphi(t)\psi(t)\varphi(t)^{-1}$.
--
--   **Formalization Note** The conjugated path is passed as a continuous path $\psi'$ together with the identity $\psi'(t)=\varphi(t)\psi(t)\varphi(t)^{-1}$ for all $t$.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (1), p. 6; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt, Proposition 8 (1), Naturality: `μ_CZ(φψφ⁻¹) = μ_CZ(ψ)` for every path `φ`
of symplectic matrices. -/
theorem czIndex_naturality {n : ℕ} (φ : C(unitInterval, Mat n))
    (hφ : ∀ t, IsSymplectic (φ t)) (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n)
    (ψ' : C(unitInterval, Mat n)) (hψ' : ∀ t, ψ' t = φ t * ψ t * (φ t)⁻¹) :
    czIndex ψ' = czIndex ψ := by sorry

end ConleyZehnder
