-- Prove2me | Theorems.Thm_DiazModulus_dalag_cor_12_24
-- name    : DiazModulus.dalag_cor_12_24
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:00.020366+00:00
-- url     : https://prove2.me/theorems/aa198185-734e-4f40-8e6c-20395287ab22
-- title:
--   DALAG Cor. 12.24, proved from Th. 12.20: if a d × ℓ matrix M over ℒ̃ has Q̄-free rows and Q̄-free columns and dℓ > d + ℓ, then rank M ≥ 2
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M$ be a $d \times \ell$ matrix with entries in $\widetilde{\mathcal L}$ whose $d$ rows are linearly independent over $\overline{\mathbb Q}$ and whose $\ell$ columns are linearly independent over $\overline{\mathbb Q}$, and assume $d\ell > d + \ell$. Then $\operatorname{rank} M \ge 2$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 12.24 (p. 436). DALAG derives it from Cor. 12.22, which gives only rank ≥ 1 for 2 × 3 matrices. Here it is proved from Th. 12.20 (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 1; on the platform DiazModulus.roy_rank_bound). Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_cor_12_24 {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hrows : LinearIndependent (↥Qbar) M.row) (hcols : LinearIndependent (↥Qbar) M.col)
    (hdl : l + d < l * d) : 2 ≤ M.rank := by
  sorry

end DiazModulus
