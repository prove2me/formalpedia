-- Prove2me | Theorems.Thm_ConleyZehnder_rhoHat_path_continuous
-- name    : ConleyZehnder.rhoHat_path_continuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T20:46:17.364988+00:00
-- url     : https://prove2.me/theorems/7f6e7c9b-bd77-41ec-9394-1279edad219f
-- title:
--   Along a continuous path of symplectic matrices, $\hat\rho$ is continuous with values in the unit circle
-- statement:
--   Let $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$. For a real $2n\times 2n$ matrix $A$ let $C_A=\tfrac12(A-J_0AJ_0)$ be its complex-linear part, $\det_{\mathbb C}C_A$ the determinant of $C_A$ viewed as a complex $n\times n$ matrix, and $\hat\rho(A)=\det_{\mathbb C}C_A/|\det_{\mathbb C}C_A|$.
--
--   Let $\chi:[0,1]\to\mathrm{Sp}(2n)$ be a continuous path of symplectic matrices. Then $t\mapsto\hat\rho(\chi(t))$ is a continuous map $[0,1]\to\mathbb C$ with $|\hat\rho(\chi(t))|=1$ for every $t$.
--
--   This is the basic regularity fact needed to speak of continuous arguments (and hence degrees) of $\hat\rho$ along paths and loops of symplectic matrices, as in the definitions of the Conley–Zehnder and Maslov indices.
--
--   Formalization note: `Mat n`, `IsSymplectic`, `complexLinearDet` and `rhoHat` come from the definition module `ConleyZehnder_Setting`; paths are continuous maps `C(unitInterval, Mat n)`. In the definition module `rhoHat A` is a quotient that would be $0$ if $\det_{\mathbb C}C_A$ vanished; the statement asserts in particular that this does not happen along $\chi$.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Section 2, formula (9) (the map rho-hat on Sp(2n)); this regularity statement is used implicitly there and is not stated in this form in the reference

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Along a continuous path of symplectic matrices, `t ↦ ρ̂(χ(t))` is continuous and takes
values in the unit circle. -/
theorem rhoHat_path_continuous {n : ℕ} (χ : C(unitInterval, Mat n))
    (hχ : ∀ t, IsSymplectic (χ t)) :
    Continuous (fun t => rhoHat (χ t)) ∧ ∀ t, ‖rhoHat (χ t)‖ = 1 := by sorry

end ConleyZehnder
