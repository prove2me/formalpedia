-- Prove2me | Theorems.Thm_BosonicLearn_fugacityFamily_promiseClass
-- name    : BosonicLearn.fugacityFamily_promiseClass
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T07:21:37.438209+00:00
-- url     : https://prove2.me/theorems/7e414cd4-ccd8-46e3-9cd7-e47039cb5a4d
-- title:
--   The hard family $\rho_{R_X}$, $X\in G_{\rm supp}$, consists of passive Gaussian states with $\Sigma\succeq(\tfrac12+\nu)I$
-- statement:
--   The states used for the single-copy lower bound belong to the class that the learner is promised.
--
--   Let $0<\nu\le1$, $0<\xi<1/32$, and let $X$ be a traceless Hermitian $n\times n$ matrix with $\|X\|_{\mathrm{op}}\le4$ (that is, $X\in G_{\mathrm{supp}}$). Put
--
--   $$
--   R_X=r\,(\mathbf 1+\xi X),\qquad r=\frac{\nu}{(1-4\xi)(1+\nu)} .
--   $$
--
--   Then $\rho_{R_X}=\det(\mathbf 1-R_X)\,\Gamma(R_X)$ is a density operator on the $n$-mode Fock space; it is a passive Gaussian state, and its covariance matrix satisfies $\Sigma\succeq(\tfrac12+\nu)\mathbf 1$.
--
--   Why it holds. Since $\|X\|_{\mathrm{op}}\le4$, $r(1-4\xi)\mathbf 1\preceq R_X\preceq r(1+4\xi)\mathbf 1\prec\mathbf 1$ and $r(1-4\xi)=\nu/(1+\nu)$. By Lemma 2, $\rho_R$ is a passive Gaussian state for $0\preceq R\prec\mathbf 1$; its covariance has eigenvalues $\tfrac12+\lambda/(1-\lambda)$ with $\lambda$ the eigenvalues of $R$, and $\lambda\ge\nu/(1+\nu)$ gives $\lambda/(1-\lambda)\ge\nu$.
--
--   Role. A learner for the promise class in particular learns every $\rho_{R_X}$, $X\in G_{\mathrm{supp}}$; this is the first step of the proof of Theorem 5 from Proposition 5.
--
--   **Formalization Note** The conclusion is the existence of a `State` with coefficient array `fugacityCoeff (fugacityFamily ν ξ X)` which satisfies `IsPassive` and lies in `promiseClass n ν`. $\Gamma(R)$ is `gammaFock`, $G_{\mathrm{supp}}$ is `Gsupp n ⊆ Herm0 n` with the operator norm `schattenNorm ⊤`. The upper bound $\Sigma\preceq(\tfrac12+2\nu)\mathbf 1$ of the paper is not needed and not stated.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, Eqs. (30)–(31), p. 30 (the family R_X = r(I + ξX)); proof of Theorem 5, p. 40 ("this family satisfies (1/2 + ν)I ≤ Σ ≤ (1/2 + 2ν)I"); Lemma 2, p. 20

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_Gsupp
import Definitions.Def_BosonicLearn_IsPassive
import Definitions.Def_BosonicLearn_promiseClass

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **The hard family consists of passive Gaussian states of the promise class.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, Eqs. (30)–(31), p. 30: "Define the following family of fugacity matrices: R_X := r(I + ξX) for
X ∈ Herm_0(n) … r := ν/((1 − 4ξ)(1 + ν))", and proof of Theorem 5, p. 40: "Note this family satisfies
(1/2 + ν)I ≤ Σ ≤ (1/2 + 2ν)I as has been shown above."

For `0 < ν ≤ 1`, `0 < ξ < 1/32` and `X ∈ G_supp` (traceless Hermitian, `‖X‖_op ≤ 4`), the array
`ρ_{R_X} = det(I − R_X) Γ(R_X)`, `R_X = r(I + ξX)`, is the coefficient array of a density operator which is a
passive Gaussian state with covariance `Σ ⪰ (½ + ν) I`.

**Formalization Note.** The conclusion gives a `State` with these coefficients, `IsPassive`, and membership in
`promiseClass n ν`. Since `‖X‖_op ≤ 4`, `r(1 − 4ξ) I ⪯ R_X ⪯ r(1 + 4ξ) I ≺ I` and `r(1 − 4ξ) = ν/(1 + ν)`; a
passive state with fugacity `R` has covariance eigenvalues `½ + λ/(1 − λ)`, `λ` the eigenvalues of `R`
(Lemma 2). -/
theorem fugacityFamily_promiseClass (n : ℕ) (ν ξ : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1 / 32) (X : Herm0 n) (hX : X ∈ Gsupp n) :
    ∃ ρ : State (Occupation (Fin n)), ρ.coefficients = fugacityCoeff (fugacityFamily ν ξ X) ∧
      IsPassive ρ ∧ ρ ∈ promiseClass n ν := by sorry

end BosonicLearn
