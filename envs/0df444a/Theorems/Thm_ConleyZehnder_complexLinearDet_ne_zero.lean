-- Prove2me | Theorems.Thm_ConleyZehnder_complexLinearDet_ne_zero
-- name    : ConleyZehnder.complexLinearDet_ne_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:20:26.479545+00:00
-- url     : https://prove2.me/theorems/03b0a956-ce4a-4b1e-b7b6-b9562534c72f
-- title:
--   The complex-linear part of a symplectic matrix is invertible
-- statement:
--   For every $A\in\mathrm{Sp}(2n)$, the complex-linear part
--   $$C_A=\tfrac12\,(A-J_0AJ_0)=\begin{pmatrix}X&-Y\\Y&X\end{pmatrix}$$
--   is invertible as a complex matrix: $\det(X+iY)\neq0$.
--
--   In particular $\hat\rho(A)=\det_{\mathbb C}C_A/|\det_{\mathbb C}C_A|$ is a well-defined point of $S^1$ for every symplectic $A$.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), proof of Corollary 12, p. 9 (formula (9)); Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt, proof of Corollary 12: for every symplectic `A`, the `ℂ`-linear part
`½(A - J₀AJ₀)` is invertible, i.e. `det_ℂ C_A ≠ 0`. -/
theorem complexLinearDet_ne_zero {n : ℕ} (A : Mat n) (hA : IsSymplectic A) :
    complexLinearDet A ≠ 0 := by sorry

end ConleyZehnder
