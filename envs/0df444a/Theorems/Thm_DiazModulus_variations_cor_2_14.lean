-- Prove2me | Theorems.Thm_DiazModulus_variations_cor_2_14
-- name    : DiazModulus.variations_cor_2_14
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:35.057888+00:00
-- url     : https://prove2.me/theorems/755d5f3e-cdb2-446b-9ca6-62aeea1a9fe6
-- title:
--   Waldschmidt 2005 (Variations), Cor. 2.14: if an m × ℓ matrix (λᵢⱼ) over ℒ has ℚ-free columns, λ₁, …, λₘ ∈ ℒ are ℚ-free and ℓ > m², then some Σᵢ λᵢλᵢⱼ ∉ ℒ̃
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M = (\lambda_{ij})$ be an $m \times \ell$ matrix with entries in $\mathcal L$ whose $\ell$ columns are linearly independent over $\mathbb Q$, let $\lambda_1, \dots, \lambda_m \in \mathcal L$ be linearly independent over $\mathbb Q$, and assume $\ell > m^2$. Then for some $j \in \{1, \dots, \ell\}$
--   $$\lambda_1\lambda_{1j} + \dots + \lambda_m\lambda_{mj} \notin \widetilde{\mathcal L}.$$
-- source:
--   M. Waldschmidt, Variations on the six exponentials theorem, in Algebra and Number Theory (Hyderabad), Hindustan Book Agency, 2005, 338–355, Cor. 2.14 (p. 347), from Th. 2.11 and Baker's theorem (DALAG, Th. 1.6), proved on the platform as Schanuel.baker_linear_forms_in_logarithms. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem variations_cor_2_14 {m ℓ : ℕ} (M : Matrix (Fin m) (Fin ℓ) ℂ) (hM : ∀ i j, M i j ∈ LogAlg)
    (hcol : LinearIndependent ℚ M.col) (l : Fin m → ℂ) (hl : ∀ i, l i ∈ LogAlg)
    (hlind : LinearIndependent ℚ l) (hℓ : m ^ 2 < ℓ) :
    ∃ j : Fin ℓ, ∑ i, l i * M i j ∉ LogAlgTilde := by
  sorry

end DiazModulus
