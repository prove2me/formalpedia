-- Prove2me | Theorems.Thm_ConleyZehnder_complexLinearDet_mul_four_pow
-- name    : ConleyZehnder.complexLinearDet_mul_four_pow
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T17:04:20.486032+00:00
-- url     : https://prove2.me/theorems/2651c0f7-e40b-492f-878e-7b0e33e80a0a
-- title:
--   $4^n\det_{\mathbb C}C_A$ as the determinant of the complex matrix $(A+\mathrm{Id})-iJ_0(A-\mathrm{Id})$
-- statement:
--   Let $A$ be a real $2n\times 2n$ matrix, $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$, and let $C_A=\tfrac12(A-J_0AJ_0)$ be the $\mathbb C$-linear part of $A$. Writing $C_A=\begin{pmatrix}X&-Y\\ Y&X\end{pmatrix}$, let $\det_{\mathbb C}C_A=\det(X+iY)$ (an $n\times n$ complex determinant). Viewing $A$ and $J_0$ as complex $2n\times 2n$ matrices,
--   $$4^n\,\det_{\mathbb C}C_A=\det\big((A+\mathrm{Id})-i\,J_0(A-\mathrm{Id})\big).$$
--
--   The identity holds for every real matrix $A$, symplectic or not. It writes the complex determinant of the $\mathbb C$-linear part, which defines $\hat\rho(A)=\det_{\mathbb C}C_A/|\det_{\mathbb C}C_A|$, as an ordinary $2n\times 2n$ determinant that depends affinely on $A$.
--
--   Formalization note: `Mat n` is the type of real matrices indexed by `Fin n ⊕ Fin n`, `J₀ n` is Mathlib's `Matrix.J`, and `complexLinearDet` is from the definition module `ConleyZehnder_Setting`; the complex matrices are obtained with `Matrix.map` and the coercion `ℝ → ℂ`.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Section 2, Corollary 12, formula (9), p. 8 (definition of the normalized complex determinant)

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- For every real `2n × 2n` matrix `A`, `4ⁿ · det_ℂ C_A` equals the determinant of the complex
`2n × 2n` matrix `(A + 1) - i J₀ (A - 1)`, where `A` and `J₀` are viewed as complex matrices. -/
theorem complexLinearDet_mul_four_pow {n : ℕ} (A : Mat n) :
    (4 : ℂ) ^ n * complexLinearDet A =
      ((A + 1).map (fun x : ℝ => (x : ℂ)) -
        Complex.I • (J₀ n * (A - 1)).map (fun x : ℝ => (x : ℂ))).det := by sorry

end ConleyZehnder
