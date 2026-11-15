-- Prove2me | Theorems.Thm_DiazModulus_variations_theorem_2_11
-- name    : DiazModulus.variations_theorem_2_11
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:42.1715+00:00
-- url     : https://prove2.me/theorems/7924bc82-5f9e-445c-b93c-fad1c930fe20
-- title:
--   Waldschmidt 2005 (Variations), Th. 2.11: if M = (Λᵢⱼ) is m × ℓ over ℒ̃, ℓ > m², and the columns of (Iₘ, M) and 1, Λ₁, …, Λₘ ∈ ℒ̃ are Q̄-free, then some Σᵢ ΛᵢΛᵢⱼ ∉ ℒ̃
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M = (\Lambda_{ij})$ be an $m \times \ell$ matrix with entries in $\widetilde{\mathcal L}$ such that the $m + \ell$ columns of the $m \times (m + \ell)$ matrix $(I_m, M)$ are linearly independent over $\overline{\mathbb Q}$. Let $\Lambda_1, \dots, \Lambda_m \in \widetilde{\mathcal L}$ be such that $1, \Lambda_1, \dots, \Lambda_m$ are linearly independent over $\overline{\mathbb Q}$, and assume $\ell > m^2$. Then for some $j \in \{1, \dots, \ell\}$
--   $$\Lambda_1\Lambda_{1j} + \dots + \Lambda_m\Lambda_{mj} \notin \widetilde{\mathcal L}.$$
-- source:
--   M. Waldschmidt, Variations on the six exponentials theorem, in Algebra and Number Theory (Hyderabad), Hindustan Book Agency, 2005, 338–355, Th. 2.11 (p. 346; proof p. 348); M. Waldschmidt, The role of complex conjugation in transcendental number theory, 2005, Th. 6.2 (p. 10). Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem variations_theorem_2_11 {m ℓ : ℕ} (M : Matrix (Fin m) (Fin ℓ) ℂ)
    (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hcol : LinearIndependent (↥Qbar) (Matrix.fromCols (1 : Matrix (Fin m) (Fin m) ℂ) M).col)
    (Λ : Fin m → ℂ) (hΛ : ∀ i, Λ i ∈ LogAlgTilde)
    (hΛind : LinearIndependent (↥Qbar) (Fin.cons 1 Λ : Fin (m + 1) → ℂ))
    (hℓ : m ^ 2 < ℓ) :
    ∃ j : Fin ℓ, ∑ i, Λ i * M i j ∉ LogAlgTilde := by
  sorry

end DiazModulus
