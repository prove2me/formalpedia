-- Prove2me | Theorems.Thm_BosonicLearn_isDensity_of_posSemidef
-- name    : BosonicLearn.isDensity_of_posSemidef
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T20:27:59.881386+00:00
-- url     : https://prove2.me/theorems/c1a8098c-5825-4059-96b4-917d0902b3e2
-- title:
--   A positive semidefinite array with trace one is a density operator (the nuclear expansion is automatic)
-- statement:
--   Positivity and normalization imply trace class.
--
--   Let $I$ be a countable index set and $X=(X_{ij})_{i,j\in I}$ a complex array such that every finite quadratic form $\sum_{i,j\in s}\bar z_iX_{ij}z_j$ is real and non-negative, and $\sum_iX_{ii}=1$. Then $X$ is a density operator on $\ell^2(I)$ in the sense of the published predicate `IsDensity`; in particular it has a nuclear expansion $X_{ij}=\sum_kl_k(i)\overline{r_k(j)}$ with $l_k,r_k\in\ell^2(I)$ and $\sum_k\|l_k\|\|r_k\|<\infty$ (one may take $l_k=r_k=X^{1/2}e_k$).
--
--   Role. `IsDensity` asks for a nuclear expansion in addition to positivity and normalization; this lemma removes that burden when states are constructed by mixing (`BosonicLearn.state_gaussian_mixture`).
--
--   **Formalization Note** `IsDensity` is `Dependency50.P33.IsDensity`; the index type is any `Countable` type.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, Eqs. (2) and (4), pp. 4–5 (Gaussian states, displacement operators, characteristic function) (states as density operators)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

namespace BosonicLearn

/-- **A positive semidefinite array with trace one is a density operator.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, pp. 4–5 (states of the n-mode Fock space as density operators: positive, trace one).

Let `I` be a countable index set and `X` an `I × I` complex array all of whose finite quadratic forms are real and
non-negative, with summable diagonal of sum `1`. Then `X` is a density operator in the sense of `IsDensity`: in
particular it is trace class (it has a nuclear expansion `X_ij = ∑ₖ lₖ(i) \overline{rₖ(j)}`, `∑ₖ ‖lₖ‖‖rₖ‖ < ∞`).

**Formalization Note.** `IsDensity` asks for a nuclear expansion in addition to positivity and normalization; this
lemma says the expansion is automatic (take `lₖ = rₖ = X^{1/2} eₖ`). It makes it possible to build states by
mixing. -/
theorem isDensity_of_posSemidef {I : Type} [Countable I] (X : Matrix I I ℂ)
    (hpsd : ∀ (s : Finset I) (z : I → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).re)
    (hsum : Summable (fun i => (X i i).re)) (htr : ∑' i, (X i i).re = 1) : IsDensity X := by sorry

end BosonicLearn
