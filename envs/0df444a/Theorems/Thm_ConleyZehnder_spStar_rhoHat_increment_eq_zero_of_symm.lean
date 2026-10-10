-- Prove2me | Theorems.Thm_ConleyZehnder_spStar_rhoHat_increment_eq_zero_of_symm
-- name    : ConleyZehnder.spStar_rhoHat_increment_eq_zero_of_symm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T10:09:41.503978+00:00
-- url     : https://prove2.me/theorems/6642ddb3-0d23-4b2c-82cf-b317d4308bbc
-- title:
--   Zero ρ̂-winding along Sp* paths between symmetric matrices
-- statement:
--   Let $\mathrm{Sp}^*(2n)$ be the set of real symplectic $2n\times 2n$ matrices $A$ ($AJ_0A^{T}=J_0$) without eigenvalue $1$, and let $\hat\rho(A)=\det_{\mathbb C}C_A/|\det_{\mathbb C}C_A|$ be the normalized complex determinant of the complex-linear part $C_A=\tfrac12(A-J_0AJ_0)$ (Gutt, formula (9)).
--
--   Let $\chi:[0,1]\to\mathrm{Sp}^*(2n)$ be a continuous path whose endpoints are symmetric matrices, $\chi(0)^{T}=\chi(0)$ and $\chi(1)^{T}=\chi(1)$. Then every continuous function $\theta:[0,1]\to\mathbb R$ with $\hat\rho(\chi(t))=e^{i\theta(t)}$ for all $t$ satisfies
--   $$\theta(1)-\theta(0)=0.$$
--
--   The matrices $W^{\pm}$ that normalize the Conley–Zehnder index, and all real diagonal symplectic matrices, are symmetric. So the statement says that a path in $\mathrm{Sp}^*$ joining such normal forms contributes nothing to the index. This is useful when an extension of a path in $\mathrm{SP}(n)$ has to be continued from one diagonal normal form to $W^{\pm}$, as for the product property (Gutt, Proposition 8 (4)).
--
--   Formalization note: `SpStar`, `rhoHat`, `IsArgLift` and `Mat n` come from the definition module `ConleyZehnder_Setting`; paths are `C(unitInterval, Mat n)`, and `IsArgLift f θ` means that `θ` is continuous with `f t = exp(i θ t)`. Symmetry is `Mᵀ = M`.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239); new lemma of this mission (used for Proposition 8 (4))

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

open Matrix

/-- Along a path in `Sp*` whose two endpoints are symmetric matrices, every continuous
argument of `ρ̂` has total increment zero. -/
theorem spStar_rhoHat_increment_eq_zero_of_symm {n : ℕ} (χ : C(unitInterval, Mat n))
    (hχ : ∀ t, χ t ∈ SpStar n) (h0 : (χ 0)ᵀ = χ 0) (h1 : (χ 1)ᵀ = χ 1)
    (θ : unitInterval → ℝ) (hθ : IsArgLift (fun t => rhoHat (χ t)) θ) :
    θ 1 - θ 0 = 0 := by sorry

end ConleyZehnder
