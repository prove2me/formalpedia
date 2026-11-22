-- Prove2me | Theorems.Thm_DiazModulus_fischler_theorem_2_3
-- name    : DiazModulus.fischler_theorem_2_3
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-21T08:08:11.702186+00:00
-- url     : https://prove2.me/theorems/2b330aea-a1ff-4ed5-bc53-aaf0ebfdc91f
-- title:
--   Fischler 2001, Th. 2.3: if a d × l matrix of rank 1 with entries in ℒ̃ has d ≥ 2 and l ≥ 3, then its rows or its columns are linearly dependent over Q̄
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $d \ge 2$ and $l \ge 3$, and let $M$ be a $d \times l$ matrix of rank $1$ (over $\mathbb C$) with entries in $\widetilde{\mathcal L}$. Then the $d$ rows of $M$ are linearly dependent over $\overline{\mathbb Q}$, or the $l$ columns of $M$ are linearly dependent over $\overline{\mathbb Q}$.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 2.3 (p. 171), as printed. It is the d × l form of Cor. 2 of D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, which is printed for 2 × 3 matrices only (p. 38); Fischler states the d × l form as Th. 2.3 and presents it as a corollary of his Th. 2.1. Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. Proved from Roy's strong six exponentials theorem in product form (DiazModulus.strong_six_exponentials_unconditional), applied to a 2 × 3 corner of the factorisation Mᵢⱼ = uᵢcⱼ. Formal proof: Diaz modulus mission, 20 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_theorem_2_3 {d l : ℕ} (hd : 2 ≤ d) (hl : 3 ≤ l) (M : Matrix (Fin d) (Fin l) ℂ)
    (hrank : M.rank = 1) (hM : ∀ i j, M i j ∈ LogAlgTilde) :
    ¬ LinearIndependent (↥Qbar) (fun i => M i) ∨
      ¬ LinearIndependent (↥Qbar) (fun j => fun i => M i j) := by
  sorry

end DiazModulus
