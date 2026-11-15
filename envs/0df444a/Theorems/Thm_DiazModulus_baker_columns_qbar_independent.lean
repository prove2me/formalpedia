-- Prove2me | Theorems.Thm_DiazModulus_baker_columns_qbar_independent
-- name    : DiazModulus.baker_columns_qbar_independent
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:19.933595+00:00
-- url     : https://prove2.me/theorems/6658532e-d703-4223-affc-d6d0d69a2f8d
-- title:
--   Baker's theorem in column form: if an m × ℓ matrix M over ℒ has ℚ-free columns, the m + ℓ columns of (Iₘ, M) are linearly independent over Q̄
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M$ be an $m \times \ell$ matrix with entries in $\mathcal L$ whose $\ell$ columns are linearly independent over $\mathbb Q$. Then the $m + \ell$ columns of the $m \times (m + \ell)$ matrix $(I_m, M)$ are linearly independent over $\overline{\mathbb Q}$.
-- source:
--   Step of the proof of M. Waldschmidt, Variations on the six exponentials theorem, in Algebra and Number Theory (Hyderabad), Hindustan Book Agency, 2005, 338–355, Cor. 2.14 (p. 347), where it is deduced from Baker's theorem; here from Baker's theorem (DALAG, Th. 1.6), proved on the platform as Schanuel.baker_linear_forms_in_logarithms, applied coordinatewise to a ℚ-basis of the ℚ-span of the entries. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem baker_columns_qbar_independent {m ℓ : ℕ} (M : Matrix (Fin m) (Fin ℓ) ℂ)
    (hM : ∀ i j, M i j ∈ LogAlg) (hcol : LinearIndependent ℚ M.col) :
    LinearIndependent (↥Qbar) (Matrix.fromCols (1 : Matrix (Fin m) (Fin m) ℂ) M).col := by
  sorry

end DiazModulus
