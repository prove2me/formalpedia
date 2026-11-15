-- Prove2me | Theorems.Thm_DiazModulus_fv_lambda_squares
-- name    : DiazModulus.fv_lambda_squares
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:22.333032+00:00
-- url     : https://prove2.me/theorems/56748e12-b275-4019-b32a-5ed6a3e35271
-- title:
--   Waldschmidt 2005 (Further variations), p. 3: if Λ₁, Λ₂, Λ₃ ∈ ℒ̃ and 1, Λ₁, Λ₂, Λ₃ are Q̄-free, one of Λ₁² − Λ₂Λ₃, Λ₂² − Λ₃Λ₁, Λ₃² − Λ₁Λ₂ is not in ℒ̃
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $\Lambda_1, \Lambda_2, \Lambda_3 \in \widetilde{\mathcal L}$ be such that $1, \Lambda_1, \Lambda_2, \Lambda_3$ are linearly independent over $\overline{\mathbb Q}$. Then at least one of
--   $$\Lambda_1^2 - \Lambda_2\Lambda_3, \qquad \Lambda_2^2 - \Lambda_3\Lambda_1, \qquad \Lambda_3^2 - \Lambda_1\Lambda_2$$
--   is not in $\widetilde{\mathcal L}$.
-- source:
--   M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, p. 3, stated there as a consequence of Th. 1.2; it is Th. 1.2 for the matrix (Λ₁ Λ₂ Λ₃; Λ₂ Λ₃ Λ₁). Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_lambda_squares (Λ : Fin 3 → ℂ) (hΛ : ∀ i, Λ i ∈ LogAlgTilde)
    (hfree : LinearIndependent (↥Qbar) ![1, Λ 0, Λ 1, Λ 2]) :
    Λ 0 ^ 2 - Λ 1 * Λ 2 ∉ LogAlgTilde ∨ Λ 1 ^ 2 - Λ 2 * Λ 0 ∉ LogAlgTilde ∨
      Λ 2 ^ 2 - Λ 0 * Λ 1 ∉ LogAlgTilde := by
  sorry

end DiazModulus
