-- Prove2me | Theorems.Thm_DiazModulus_variations_cor_3_2
-- name    : DiazModulus.variations_cor_3_2
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:39.236841+00:00
-- url     : https://prove2.me/theorems/4d8ea357-402b-462f-b050-c39d00f044e7
-- title:
--   Waldschmidt 2005 (Variations), Cor. 3.2: if an m × ℓ matrix (Λᵢⱼ) over ℒ̃ has Q̄-free columns, x₁, …, xₘ ∈ ℂ are Q̄-free and ℓ > m(m − 1), then Σᵢ xᵢΛᵢⱼ ≠ 0 for some j
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M = (\Lambda_{ij})$ be an $m \times \ell$ matrix with entries in $\widetilde{\mathcal L}$ whose $\ell$ columns are linearly independent over $\overline{\mathbb Q}$, let $x_1, \dots, x_m \in \mathbb C$ be linearly independent over $\overline{\mathbb Q}$, and assume $\ell > m(m - 1)$. Then for some $j \in \{1, \dots, \ell\}$
--   $$x_1\Lambda_{1j} + \dots + x_m\Lambda_{mj} \ne 0.$$
-- source:
--   M. Waldschmidt, Variations on the six exponentials theorem, in Algebra and Number Theory (Hyderabad), Hindustan Book Agency, 2005, 338–355, Cor. 3.2 (p. 348), from Th. 3.1. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem variations_cor_3_2 {m ℓ : ℕ} (M : Matrix (Fin m) (Fin ℓ) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hcol : LinearIndependent (↥Qbar) M.col) (x : Fin m → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hℓ : m * (m - 1) < ℓ) :
    ∃ j : Fin ℓ, ∑ i, x i * M i j ≠ 0 := by
  sorry

end DiazModulus
