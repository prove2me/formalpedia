-- Prove2me | Theorems.Thm_DiazModulus_fv_cor_1_4
-- name    : DiazModulus.fv_cor_1_4
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:17.782206+00:00
-- url     : https://prove2.me/theorems/291e8987-bac1-47fe-a356-537978a9ce3e
-- title:
--   Waldschmidt 2005 (Further variations), Cor. 1.4: if λ ∈ ℒ²ˣ³ has ℚ-free rows and ℚ-free columns, one of λ₁₁λ₂₂ − λ₁₂λ₂₁, λ₁₂λ₂₃ − λ₁₃λ₂₂, λ₁₃λ₂₁ − λ₁₁λ₂₃ is not in ℒ̃
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $\lambda = (\lambda_{ij})$ be a $2 \times 3$ matrix with entries in $\mathcal L$ whose two rows are linearly independent over $\mathbb Q$ (in $\mathbb C^3$) and whose three columns are linearly independent over $\mathbb Q$ (in $\mathbb C^2$). Then at least one of
--   $$\lambda_{11}\lambda_{22} - \lambda_{12}\lambda_{21}, \qquad \lambda_{12}\lambda_{23} - \lambda_{13}\lambda_{22}, \qquad \lambda_{13}\lambda_{21} - \lambda_{11}\lambda_{23}$$
--   is not in $\widetilde{\mathcal L}$.
-- source:
--   M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Cor. 1.4 (pp. 3–4; proof p. 8), from Th. 1.2 and Baker's theorem (DALAG, Th. 1.6), proved on the platform as Schanuel.baker_linear_forms_in_logarithms. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_cor_1_4 (L : Matrix (Fin 2) (Fin 3) ℂ) (hL : ∀ i j, L i j ∈ LogAlg)
    (hrows : LinearIndependent ℚ L.row) (hcols : LinearIndependent ℚ L.col) :
    L 0 0 * L 1 1 - L 0 1 * L 1 0 ∉ LogAlgTilde ∨
      L 0 1 * L 1 2 - L 0 2 * L 1 1 ∉ LogAlgTilde ∨
      L 0 2 * L 1 0 - L 0 0 * L 1 2 ∉ LogAlgTilde := by
  sorry

end DiazModulus
