-- Prove2me | Theorems.Thm_BosonicLearn_fugacity_photon_number
-- name    : BosonicLearn.fugacity_photon_number
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:32:47.609216+00:00
-- url     : https://prove2.me/theorems/58565766-0d7c-4f4c-bf8a-9555035b0492
-- title:
--   Mean photon number of $\det(I-R)\Gamma(R)$ is $\mathrm{Tr}[R(I-R)^{-1}]$
-- statement:
--   The mean photon number of the passive Gaussian state with fugacity matrix $R$.
--
--   Let $R$ be a positive semidefinite $n\times n$ complex matrix such that $1-R$ is positive definite, and $\rho_R=\det(1-R)\Gamma(R)$. Then
--
--   $$
--   \sum_{u\in\mathbb N^n}|u|\,\langle u|\rho_R|u\rangle=\operatorname{Tr}\big[R(1-R)^{-1}\big],\qquad |u|=\textstyle\sum_iu_i .
--   $$
--
--   Role. This is clause 4 of Lemma 2 of the paper ("the mean total photon number of $\rho$ is $\operatorname{Tr}(\rho\hat n)=\operatorname{Tr}[R(I-R)^{-1}]$"), and it gives the finite-energy clause of `IsGaussianState` for these states.
--
--   **Formalization Note** Stated exactly as clause 4 of `BosonicLearn.lemma_2`: the series is taken in $[0,\infty]$ (`ENNReal.ofReal` of $|u|$ times `ENNReal.ofReal` of the real part of the diagonal entry), and the right-hand side is `ENNReal.ofReal` of the real part of the trace.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2 and Eq. (21), p. 20 (passive Gaussian states as det(I − R)Γ(R)); "the mean total photon number of ρ is Tr(ρn̂) = Tr[R(I − R)^{−1}]"

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

namespace BosonicLearn

/-- **Mean photon number of `det(I − R)Γ(R)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, p. 20: "Moreover, the mean total photon number of ρ is Tr(ρn̂) = Tr[R(I − R)^{−1}]."

If `R` is positive semidefinite and `1 − R` is positive definite, then
`∑ᵤ |u| ⟨u|det(1 − R)Γ(R)|u⟩ = Tr[R(1 − R)⁻¹]`.

**Formalization Note.** Clause 4 of `lemma_2`, with the same form: the series is taken in `ℝ≥0∞`, and the real part
of the (real) trace on the right. -/
theorem fugacity_photon_number {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) :
    ∑' u : Occupation (Fin n), ENNReal.ofReal (∑ i, (u i : ℝ)) * ENNReal.ofReal (fugacityCoeff R u u).re =
      ENNReal.ofReal (R * (1 - R)⁻¹).trace.re := by sorry

end BosonicLearn
