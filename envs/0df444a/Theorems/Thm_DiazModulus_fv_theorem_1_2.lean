-- Prove2me | Theorems.Thm_DiazModulus_fv_theorem_1_2
-- name    : DiazModulus.fv_theorem_1_2
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:35.824904+00:00
-- url     : https://prove2.me/theorems/819773b1-4ee7-43bc-a05b-20927db562ed
-- title:
--   Waldschmidt 2005 (Further variations), Th. 1.2: if M ∈ ℒ̃²ˣ³ and the five rows of (M; I₃) and the five columns of (I₂, M) are Q̄-free, one of the three 2 × 2 minors of M is not in ℒ̃
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M = (\Lambda_{ij})$ be a $2 \times 3$ matrix with entries in $\widetilde{\mathcal L}$. Assume that the five rows of the $5 \times 3$ matrix $\begin{pmatrix} M \\ I_3 \end{pmatrix}$ are linearly independent over $\overline{\mathbb Q}$, and that the five columns of the $2 \times 5$ matrix $(I_2, M)$ are linearly independent over $\overline{\mathbb Q}$. Then at least one of
--   $$\Lambda_{12}\Lambda_{23} - \Lambda_{13}\Lambda_{22}, \qquad \Lambda_{13}\Lambda_{21} - \Lambda_{11}\Lambda_{23}, \qquad \Lambda_{11}\Lambda_{22} - \Lambda_{12}\Lambda_{21}$$
--   is not in $\widetilde{\mathcal L}$.
-- source:
--   M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 1.2 (pp. 2–3; proof p. 7, through Th. 2.1 and the estimate (3.1)). Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_theorem_1_2 (M : Matrix (Fin 2) (Fin 3) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hrows : LinearIndependent (↥Qbar) (Matrix.fromRows M (1 : Matrix (Fin 3) (Fin 3) ℂ)).row)
    (hcols : LinearIndependent (↥Qbar) (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) M).col) :
    M 0 1 * M 1 2 - M 0 2 * M 1 1 ∉ LogAlgTilde ∨
      M 0 2 * M 1 0 - M 0 0 * M 1 2 ∉ LogAlgTilde ∨
      M 0 0 * M 1 1 - M 0 1 * M 1 0 ∉ LogAlgTilde := by
  sorry

end DiazModulus
