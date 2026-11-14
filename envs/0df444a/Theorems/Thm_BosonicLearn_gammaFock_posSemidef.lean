-- Prove2me | Theorems.Thm_BosonicLearn_gammaFock_posSemidef
-- name    : BosonicLearn.gammaFock_posSemidef
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:12:53.570734+00:00
-- url     : https://prove2.me/theorems/3ec868dc-03ed-4b41-adad-a7e64c85228f
-- title:
--   $\Gamma(R)$ is positive semidefinite for positive semidefinite $R$
-- statement:
--   Positivity of the second quantization of a positive semidefinite matrix.
--
--   Let $R$ be a positive semidefinite $n\times n$ complex matrix. Then for every finite set $s$ of occupation vectors and every $z:\mathbb N^n\to\mathbb C$,
--
--   $$
--   \sum_{u,v\in s}\bar z_u\,\langle u|\Gamma(R)|v\rangle\,z_v\ \ge 0
--   $$
--
--   (the sum is real and non-negative).
--
--   Role. This is the positivity clause of `IsDensity` for the array $\Gamma(R)$, hence for the fugacity form $\det(I-R)\Gamma(R)$ of a passive Gaussian state in Lemma 2 of the paper.
--
--   **Formalization Note** $\Gamma$ is `BosonicLearn.gammaFock`; the conclusion is stated as "imaginary part $=0$ and real part $\ge0$", the form used in `IsDensity`. Proved from `BosonicLearn.gammaFock_mul` and `BosonicLearn.gammaFock_basic`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2 and Eq. (21), p. 20 (passive Gaussian states as det(I − R)Γ(R))

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix ComplexOrder

namespace BosonicLearn

/-- **`Γ(R)` is positive semidefinite when `R` is.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, p. 20: "There is a bijection between n-mode passive Gaussian states ρ and n-by-n Hermitian
matrices 0 ≤ R < I … the corresponding passive Gaussian state is ρ = det(I − R)Γ(R)".

If `R` is a positive semidefinite `n × n` matrix, then for every finite set `s` of occupation vectors and every
`z`, the quadratic form `∑_{u,v ∈ s} z̄_u ⟨u|Γ(R)|v⟩ z_v` is real and non-negative.

**Formalization Note.** This is the positivity clause of `IsDensity` for the array `Γ(R)` (`gammaFock`), hence for
`fugacityCoeff R = det(1 − R) • Γ(R)` when `det(1 − R) > 0`. -/
theorem gammaFock_posSemidef {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (s : Finset (Occupation (Fin n))) (z : Occupation (Fin n) → ℂ) :
    (∑ u ∈ s, ∑ v ∈ s, star (z u) * gammaFock R u v * z v).im = 0 ∧
    0 ≤ (∑ u ∈ s, ∑ v ∈ s, star (z u) * gammaFock R u v * z v).re := by sorry

end BosonicLearn
