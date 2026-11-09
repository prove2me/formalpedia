-- Prove2me | Theorems.Thm_BosonicLearn_lemma_2
-- name    : BosonicLearn.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:36:17.713755+00:00
-- url     : https://prove2.me/theorems/fa654cc2-3195-4126-9112-e133fa7110b8
-- title:
--   Lemma 2 — passive Gaussian states are $\det(I-R)\Gamma(R)$ for fugacity matrices $0\preceq R\prec I$
-- statement:
--   1. For every Hermitian $R\in\mathbb C^{n\times n}$ with $0\preceq R\prec I$, $\rho_R=\det(I-R)\Gamma(R)$ is a passive Gaussian state.
--   2. Every passive Gaussian state equals $\rho_R$ for exactly one such $R$ (so $R\mapsto\rho_R$ is a bijection).
--   3. That $R$ is recovered from the vacuum and one-photon sectors: $R=P_1\rho P_1/\operatorname{Tr}(P_0\rho)$, i.e. $R_{ij}=\langle e_i|\rho|e_j\rangle/\langle0|\rho|0\rangle$.
--   4. The mean total photon number is
--   $$\operatorname{Tr}(\rho_R\hat n)=\operatorname{Tr}\big[R(I-R)^{-1}\big].$$
--
--   The fugacity matrix is the parametrization of passive states used in all the lower bounds.
--
--   Differences from the source:
--   - encoding: a bijection between passive Gaussian states and Hermitian 0 ≤ R < I → clause 1 (ρ_R is a passive Gaussian state) and clause 2 (each passive state is ρ_R for exactly one R); reason: the two clauses are surjectivity and injectivity
--   - encoding: Tr(ρn̂) = Tr[R(I − R)^{-1}] → ∑_u |u| ρ_uu in ℝ≥0∞ equals the real part of Tr[R(I − R)^{-1}]; reason: the photon-number series has nonnegative terms; the trace is real for such R
--   - encoding: Γ(X) := ⊕_m X^{⊗m}|Sym^m → the Fock-basis formula for Γ(R) (sum over integer matrices with row sums u, column sums v); reason: the standard matrix elements of Γ(R); the paper prints no basis formula
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2, Eqs. (21)–(22), p. 20

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_IsPassive
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix
open scoped ComplexOrder

namespace BosonicLearn

/-- **Lemma 2 (Fugacity matrix representation).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, Eqs. (21)–(22), p. 20: "There is a bijection between n-mode passive Gaussian states ρ and n-by-n
Hermitian matrices 0 ≤ R < I. Given R, which we call the fugacity matrix, the corresponding passive Gaussian state
is ρ = det(I − R)Γ(R) … Conversely, if P_0 and P_1 denote the projectors onto the vacuum and one-photon sectors,
respectively, then R = P_1ρP_1/Tr(P_0ρ), where the one-photon sector is naturally identified with ℂⁿ. Moreover, the
mean total photon number of ρ is Tr(ρn̂) = Tr[R(I − R)^{−1}]."

1. For every Hermitian `R` with `0 ⪯ R ≺ I`, `det(I − R)Γ(R)` is (the coefficient array of) a passive Gaussian state.
2. Every passive Gaussian state is `det(I − R)Γ(R)` for exactly one Hermitian `R` with `0 ⪯ R ≺ I`.
3. For that `R`, `R_ij = ⟨e_i|ρ|e_j⟩ / ⟨0|ρ|0⟩`, with `e_i` the one-photon occupation of mode `i`.
4. For every Hermitian `0 ⪯ R ≺ I`, the mean photon number `∑_u |u| ⟨u|ρ_R|u⟩` equals `Tr[R(I − R)^{−1}]`.

**Formalization Note.** Clauses 1 and 2 together are the bijection. The photon number is the series
`∑_u (∑ᵢ uᵢ) ρ_uu` in `ℝ≥0∞`; `Tr[R(I−R)^{−1}]` is real for such `R`, and its real part is taken. -/
theorem lemma_2 {n : ℕ} :
    (∀ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef → (1 - R).PosDef →
      ∃ ρ : State (Occupation (Fin n)), ρ.coefficients = fugacityCoeff R ∧ IsPassive ρ) ∧
    (∀ ρ : State (Occupation (Fin n)), IsPassive ρ →
      ∃! R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ (1 - R).PosDef ∧ ρ.coefficients = fugacityCoeff R) ∧
    (∀ (ρ : State (Occupation (Fin n))) (R : Matrix (Fin n) (Fin n) ℂ),
      R.PosSemidef → (1 - R).PosDef → ρ.coefficients = fugacityCoeff R →
      ∀ i j : Fin n, R i j = ρ.coefficients (Pi.single i 1) (Pi.single j 1) / ρ.coefficients 0 0) ∧
    (∀ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef → (1 - R).PosDef →
      ∑' u : Occupation (Fin n), ENNReal.ofReal (∑ i, (u i : ℝ)) * ENNReal.ofReal (fugacityCoeff R u u).re =
        ENNReal.ofReal (R * (1 - R)⁻¹).trace.re) := by sorry

end BosonicLearn
