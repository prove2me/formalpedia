-- Prove2me | Theorems.Thm_DiazModulus_role_cor_6_3
-- name    : DiazModulus.role_cor_6_3
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:21.034918+00:00
-- url     : https://prove2.me/theorems/df983fc9-c5d3-4ac6-9bd3-3dd08855acd0
-- title:
--   Waldschmidt 2005 (Role), Cor. 6.3: if M = (Λᵢⱼ) is 2 × 5 over ℒ̃ and 1, Λ₁₁, Λ₂₁ and the columns of (I₂, M) are Q̄-free, then Λ₁₁Λ₂ⱼ − Λ₂₁Λ₁ⱼ ∉ ℒ̃ for some j ∈ {2, …, 5}
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M = (\Lambda_{ij})$ be a $2 \times 5$ matrix with entries in $\widetilde{\mathcal L}$ such that $1, \Lambda_{11}, \Lambda_{21}$ are linearly independent over $\overline{\mathbb Q}$ and the seven columns of the $2 \times 7$ matrix $(I_2, M)$ are linearly independent over $\overline{\mathbb Q}$. Then for some $j \in \{2, 3, 4, 5\}$
--   $$\Lambda_{11}\Lambda_{2j} - \Lambda_{21}\Lambda_{1j} \notin \widetilde{\mathcal L}.$$
-- source:
--   M. Waldschmidt, The role of complex conjugation in transcendental number theory, 2005, Cor. 6.3 (pp. 10–11), the corrected form of M. Waldschmidt, Variations on the six exponentials theorem, in Algebra and Number Theory (Hyderabad), Hindustan Book Agency, 2005, 338–355, Cor. 2.12 (p. 346). The printed Cor. 2.12 is false as stated; the author corrected it in M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, §4 (p. 8), and in The role of complex conjugation, Cor. 6.3, where the hypothesis 'Λ₂₁ ≠ 0 and Λ₁₁/Λ₂₁ transcendental' becomes '1, Λ₁₁, Λ₂₁ linearly independent over Q̄'. This node is the corrected form. Its proof is the printed one: Variations Th. 2.11 with m = 2, ℓ = 5, Λ₁ = −Λ₂₁, Λ₂ = Λ₁₁. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem role_cor_6_3 (M : Matrix (Fin 2) (Fin 5) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (h1 : LinearIndependent (↥Qbar) ![1, M 0 0, M 1 0])
    (hcol : LinearIndependent (↥Qbar) (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) M).col) :
    ∃ j : Fin 5, j ≠ 0 ∧ M 0 0 * M 1 j - M 1 0 * M 0 j ∉ LogAlgTilde := by
  sorry

end DiazModulus
