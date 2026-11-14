-- Prove2me | Theorems.Thm_BosonicLearn_fugacityCoeff_isDensity
-- name    : BosonicLearn.fugacityCoeff_isDensity
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:30:42.905955+00:00
-- url     : https://prove2.me/theorems/618801a6-7b2c-45f6-8853-0a058f040f8d
-- title:
--   $\det(I-R)\,\Gamma(R)$ is a density operator for Hermitian $0\preceq R\prec I$
-- statement:
--   The fugacity form defines a state.
--
--   Let $R$ be a positive semidefinite $n\times n$ complex matrix such that $1-R$ is positive definite. Then the array
--
--   $$
--   \rho_R=\det(1-R)\,\Gamma(R)
--   $$
--
--   is a density operator on the Fock space $\ell^2(\mathbb N^n)$: it is trace class, positive semidefinite, and has trace one.
--
--   Role. First half of clause 1 of Lemma 2 of the paper ("the corresponding passive Gaussian state is $\rho=\det(I-R)\Gamma(R)$"); it makes `fugacityCoeff R` the coefficient array of a `State`.
--
--   **Formalization Note** `fugacityCoeff R` is the mission definition $\det(1-R)\cdot\Gamma(R)$; `IsDensity` is the published predicate (existence of a nuclear expansion, real non-negative finite quadratic forms, summable diagonal with sum $1$).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2 and Eq. (21), p. 20 (passive Gaussian states as det(I − R)Γ(R))

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix ComplexOrder

namespace BosonicLearn

/-- **`det(I − R)Γ(R)` is a density operator.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, Eq. (21), p. 20: "Given R, which we call the fugacity matrix, the corresponding passive Gaussian state is
ρ = det(I − R)Γ(R)."

If `R` is positive semidefinite and `1 − R` is positive definite, then the array `fugacityCoeff R = det(1 − R)·Γ(R)`
is a density operator on the Fock space `ℓ²(ℕⁿ)`: trace class, positive semidefinite, of trace one.

**Formalization Note.** `IsDensity` is the published predicate (nuclear expansion, non-negative finite quadratic
forms, summable diagonal with sum `1`). -/
theorem fugacityCoeff_isDensity {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) : IsDensity (fugacityCoeff R) := by sorry

end BosonicLearn
