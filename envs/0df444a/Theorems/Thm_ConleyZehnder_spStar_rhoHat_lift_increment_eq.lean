-- Prove2me | Theorems.Thm_ConleyZehnder_spStar_rhoHat_lift_increment_eq
-- name    : ConleyZehnder.spStar_rhoHat_lift_increment_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T16:13:37.027521+00:00
-- url     : https://prove2.me/theorems/72598388-2fed-47b6-91ad-117dbab54dba
-- title:
--   Along paths in $\mathrm{Sp}^*(2n)$ the increment of $\arg\hat\rho$ depends only on the endpoints
-- statement:
--   Let $\mathrm{Sp}^*(2n)$ be the set of real symplectic $2n\times 2n$ matrices without eigenvalue $1$, and let $\hat\rho(A)=\det_{\mathbb C}C_A/|\det_{\mathbb C}C_A|$ be the normalized complex determinant of the $\mathbb C$-linear part $C_A=\tfrac12(A-J_0AJ_0)$.
--
--   Let $\chi,\chi':[0,1]\to\mathrm{Sp}^*(2n)$ be continuous paths with $\chi(0)=\chi'(0)$ and $\chi(1)=\chi'(1)$, and let $\theta,\theta':[0,1]\to\mathbb R$ be continuous with $\hat\rho(\chi(t))=e^{i\theta(t)}$ and $\hat\rho(\chi'(t))=e^{i\theta'(t)}$ for all $t$. Then
--   $$\theta(1)-\theta(0)=\theta'(1)-\theta'(0).$$
--
--   This is the uniqueness half of the definition of the Conley–Zehnder index: the degree $\deg(\hat\rho^2\circ\tilde\psi)$ does not depend on the chosen extension $\tilde\psi$ of $\psi\in\mathrm{SP}(n)$ through $\mathrm{Sp}^*(2n)$.
--
--   Formalization note: paths are `C(unitInterval, Mat n)`; "continuous argument" is the predicate `IsArgLift` of the definition module `ConleyZehnder_Setting`, and $\hat\rho$ is `rhoHat`. The statement is about arbitrary continuous arguments of $\hat\rho\circ\chi$ and $\hat\rho\circ\chi'$.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Section 2, paragraph before Definition 7 (the degree does not depend on the extension), p. 6, and Corollary 12, formulas (8)-(9), p. 8; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt §2, before Definition 7: for two paths in `Sp*` with the same endpoints, the
increments of continuous arguments of `ρ̂` along them coincide. -/
theorem spStar_rhoHat_lift_increment_eq {n : ℕ} (χ χ' : C(unitInterval, Mat n))
    (hχ : ∀ t, χ t ∈ SpStar n) (hχ' : ∀ t, χ' t ∈ SpStar n)
    (h0 : χ 0 = χ' 0) (h1 : χ 1 = χ' 1) (θ θ' : unitInterval → ℝ)
    (hθ : IsArgLift (fun t => rhoHat (χ t)) θ)
    (hθ' : IsArgLift (fun t => rhoHat (χ' t)) θ') :
    θ 1 - θ 0 = θ' 1 - θ' 0 := by sorry

end ConleyZehnder
