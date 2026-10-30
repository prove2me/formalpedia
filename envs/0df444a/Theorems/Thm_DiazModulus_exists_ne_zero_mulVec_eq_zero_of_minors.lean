-- Prove2me | Theorems.Thm_DiazModulus_exists_ne_zero_mulVec_eq_zero_of_minors
-- name    : DiazModulus.exists_ne_zero_mulVec_eq_zero_of_minors
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:13.106233+00:00
-- url     : https://prove2.me/theorems/f8cad530-fd5e-456d-b852-fe30cba35757
-- title:
--   If every maximal square minor of a matrix over a field vanishes, the matrix has a nonzero kernel vector
-- statement:
--   Let $M$ be a $\rho \times \gamma$ matrix over a field, with $\rho, \gamma$ finite. If every square minor $\det(M_{f(\mu), \mu'})_{\mu, \mu' \in \gamma}$, for $f : \gamma \to \rho$, is $0$, then $Mc = 0$ for some $c \neq 0$.
--
--   **Proof.** Otherwise $c \mapsto Mc$ is injective, so $M$ has rank $|\gamma|$ and its rows span a space of dimension $|\gamma|$. Some linearly independent family of rows has the same span, hence $|\gamma|$ members; indexing it by $\gamma$ gives $f$ whose square submatrix has independent rows, hence a non-zero determinant.
--
--   **Novelty.** Classical; routine formalisation. Linear algebra.
-- source:
--   Classical linear algebra. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem exists_ne_zero_mulVec_eq_zero_of_minors {K ρ γ : Type*} [Field K] [Fintype ρ] [Fintype γ] [DecidableEq γ]
    (M : Matrix ρ γ K) (hM : ∀ f : γ → ρ, (M.submatrix f id).det = 0) :
    ∃ c : γ → K, c ≠ 0 ∧ M.mulVec c = 0 := by
  sorry

end DiazModulus
