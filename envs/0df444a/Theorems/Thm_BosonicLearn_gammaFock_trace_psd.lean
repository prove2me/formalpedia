-- Prove2me | Theorems.Thm_BosonicLearn_gammaFock_trace_psd
-- name    : BosonicLearn.gammaFock_trace_psd
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:28:41.445962+00:00
-- url     : https://prove2.me/theorems/70e14863-af59-490b-931d-7cb550e1ff96
-- title:
--   Trace of $\Gamma(R)$: $\sum_u\langle u|\Gamma(R)|u\rangle=1/\det(1-R)$ for Hermitian $0\preceq R\prec1$
-- statement:
--   The normalization of the fugacity form of a passive Gaussian state.
--
--   Let $R$ be a positive semidefinite $n\times n$ complex matrix such that $1-R$ is positive definite. Then $\det(1-R)$ is a positive real number, and
--
--   $$
--   \sum_{u\in\mathbb N^n}\langle u|\Gamma(R)|u\rangle=\frac1{\det(1-R)} .
--   $$
--
--   Role. In Lemma 2 of the paper the passive Gaussian state with fugacity matrix $R$ is $\det(I-R)\Gamma(R)$; this is the statement that it has trace one.
--
--   **Formalization Note** $\Gamma$ is `BosonicLearn.gammaFock`. The conclusion is a conjunction: `0 < (det (1 - R)).re`, `(det (1 - R)).im = 0`, and `HasSum` over all occupation vectors with value `(det (1 - R))⁻¹`. General case of `BosonicLearn.gammaFock_trace` (diagonal $R$).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2 and Eq. (21), p. 20 (passive Gaussian states as det(I − R)Γ(R))

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix ComplexOrder

namespace BosonicLearn

/-- **Trace of `Γ(R)`: `Tr Γ(R) = 1/det(1 − R)` for Hermitian `0 ⪯ R ≺ 1`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, Eq. (21), p. 20: "the corresponding passive Gaussian state is ρ = det(I − R)Γ(R)"; the factor `det(I − R)` is the
normalization `1/Tr Γ(R)`.

If `R` is positive semidefinite and `1 − R` is positive definite, then `det(1 − R)` is a positive real number and
the diagonal Fock entries of `Γ(R)` sum, over all occupation vectors `u ∈ ℕⁿ`, to `1/det(1 − R)`.

**Formalization Note.** General case of `gammaFock_trace` (diagonal `R`), by unitary diagonalization and cyclicity
of the trace on each photon-number sector. -/
theorem gammaFock_trace_psd {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) :
    0 < ((1 - R).det).re ∧ ((1 - R).det).im = 0 ∧
    HasSum (fun u : Occupation (Fin n) => gammaFock R u u) ((1 - R).det)⁻¹ := by sorry

end BosonicLearn
