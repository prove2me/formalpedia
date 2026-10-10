-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_unique
-- name    : ConleyZehnder.czIndex_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:23:58.014898+00:00
-- url     : https://prove2.me/theorems/6ae74b4a-b33f-4bd6-ac47-94e56a09cd7e
-- title:
--   Homotopy, loop and signature determine the Conley–Zehnder index
-- statement:
--   Let $\mu$ assign an integer to each path and suppose that on $\mathrm{SP}(n)$ it has the homotopy property (constant on connected components of $\mathrm{SP}(n)$), the loop property ($\mu(\varphi\psi)=\mu(\psi)+2\mu(\varphi)$ for every symplectic loop $\varphi$ at $\mathrm{Id}$) and the signature property ($\mu(t\mapsto\exp(tJ_0S))=\tfrac12\mathrm{Sign}(S)$ for symmetric nondegenerate $S$ with all eigenvalues of absolute value $<2\pi$). Then
--   $$\mu(\psi)=\mu_{CZ}(\psi)\qquad\text{for every }\psi\in\mathrm{SP}(n).$$
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 9, p. 7; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt, Proposition 9: the homotopy, loop and signature properties characterize the
Conley–Zehnder index: every `μ : SP(n) → ℤ` with these properties equals `μ_CZ` on `SP(n)`. -/
theorem czIndex_unique {n : ℕ} (μ : C(unitInterval, Mat n) → ℤ) (hH : HomotopyAxiom μ)
    (hL : LoopAxiom μ) (hS : SignatureAxiom μ) (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) :
    μ ψ = czIndex ψ := by sorry

end ConleyZehnder
