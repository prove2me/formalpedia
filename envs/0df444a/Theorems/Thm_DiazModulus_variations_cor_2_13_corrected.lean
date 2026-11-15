-- Prove2me | Theorems.Thm_DiazModulus_variations_cor_2_13_corrected
-- name    : DiazModulus.variations_cor_2_13_corrected
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:37.191693+00:00
-- url     : https://prove2.me/theorems/79865f83-83e4-4c69-a114-3e1317e5f6d7
-- title:
--   Waldschmidt 2005 (Variations), Cor. 2.13, corrected: if (Λᵢⱼ) ∈ ℒ̃²ˣ³, Λ₁₁, Λ₂₁ ∈ ℝ ∪ iℝ, and 1, Λ₁₁, Λ₂₁ and 1, Λ₂₁, Λ₂₂, Λ₂₃, Λ̄₂₂, Λ̄₂₃ are Q̄-free, then Λ₁₁Λ₂₂ − Λ₂₁Λ₁₂ or Λ₁₁Λ₂₃ − Λ₂₁Λ₁₃ ∉ ℒ̃
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M = (\Lambda_{ij})$ be a $2 \times 3$ matrix with entries in $\widetilde{\mathcal L}$. Assume that $\Lambda_{11}$ and $\Lambda_{21}$ are each real or purely imaginary ($\overline{\Lambda_{11}} = \pm\Lambda_{11}$ and $\overline{\Lambda_{21}} = \pm\Lambda_{21}$), that $1, \Lambda_{11}, \Lambda_{21}$ are linearly independent over $\overline{\mathbb Q}$, and that the six numbers $1, \Lambda_{21}, \Lambda_{22}, \Lambda_{23}, \overline{\Lambda_{22}}, \overline{\Lambda_{23}}$ are linearly independent over $\overline{\mathbb Q}$. Then at least one of
--   $$\Lambda_{11}\Lambda_{22} - \Lambda_{21}\Lambda_{12}, \qquad \Lambda_{11}\Lambda_{23} - \Lambda_{21}\Lambda_{13}$$
--   is not in $\widetilde{\mathcal L}$.
-- source:
--   M. Waldschmidt, Variations on the six exponentials theorem, in Algebra and Number Theory (Hyderabad), Hindustan Book Agency, 2005, 338–355, Cor. 2.13 (p. 346; proof p. 347), with a corrected hypothesis. The printed Cor. 2.13 is false as stated: Λ₁₁ = 1, Λ₁₂ = Λ₁₃ = 0, Λ₂₁ = log 2, Λ₂₂ = Log(2 + i), Λ₂₃ = Log(3 + 2i) (principal logarithms) satisfy its hypotheses, the six numbers 1, log 2, Log(2 ± i), Log(3 ± 2i) being linearly independent over Q̄ by Baker's theorem, while Λ₁₁Λ₂₂ − Λ₂₁Λ₁₂ = Log(2 + i) and Λ₁₁Λ₂₃ − Λ₂₁Λ₁₃ = Log(3 + 2i) lie in ℒ. This node assumes instead that 1, Λ₁₁, Λ₂₁ are linearly independent over Q̄ (in place of 'Λ₂₁ ≠ 0 and Λ₁₁/Λ₂₁ transcendental'), as in M. Waldschmidt, The role of complex conjugation in transcendental number theory, 2005, Cor. 6.3; the printed hypothesis Λ₁₂, Λ₁₃ ∈ ℝ ∪ iℝ is not assumed. The printed proof applies Cor. 2.12 to the matrix with the conjugate columns (Λ̄₁ⱼ, Λ̄₂ⱼ), j = 2, 3; it needs signs on these columns when Λ₁₁ and Λ₂₁ are of different type (one real, the other purely imaginary). The proof here applies Role Cor. 6.3 to the columns (ε₂Λ̄₁ⱼ, ε₁Λ̄₂ⱼ), where Λ̄₁₁ = ε₁Λ₁₁ and Λ̄₂₁ = ε₂Λ₂₁ with ε₁, ε₂ ∈ {1, −1}. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem variations_cor_2_13_corrected (M : Matrix (Fin 2) (Fin 3) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (h₁₁ : conj (M 0 0) = M 0 0 ∨ conj (M 0 0) = -M 0 0)
    (h₂₁ : conj (M 1 0) = M 1 0 ∨ conj (M 1 0) = -M 1 0)
    (h1 : LinearIndependent (↥Qbar) ![1, M 0 0, M 1 0])
    (h6 : LinearIndependent (↥Qbar) ![1, M 1 0, M 1 1, M 1 2, conj (M 1 1), conj (M 1 2)]) :
    M 0 0 * M 1 1 - M 1 0 * M 0 1 ∉ LogAlgTilde ∨ M 0 0 * M 1 2 - M 1 0 * M 0 2 ∉ LogAlgTilde := by
  sorry

end DiazModulus
