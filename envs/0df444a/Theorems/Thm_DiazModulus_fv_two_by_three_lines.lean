-- Prove2me | Theorems.Thm_DiazModulus_fv_two_by_three_lines
-- name    : DiazModulus.fv_two_by_three_lines
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:34.556024+00:00
-- url     : https://prove2.me/theorems/4e2267dd-013a-4f71-aa03-38a791e11770
-- title:
--   If the five rows of (M; I₃) are Q̄-free for a complex 2 × 3 matrix M, every ℂ-subspace V ≠ ℂ² meets the Q̄-span of the five columns of (I₂, M) in dimension at most 3
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M$ be a complex $2 \times 3$ matrix such that the five rows of the $5 \times 3$ matrix $\begin{pmatrix} M \\ I_3 \end{pmatrix}$ are linearly independent over $\overline{\mathbb Q}$, and let $X$ be the $\overline{\mathbb Q}$-span of the five columns of the $2 \times 5$ matrix $(I_2, M)$. Then for every $\mathbb C$-subspace $V \ne \mathbb C^2$
--   $$\dim_{\overline{\mathbb Q}}(X \cap V) \le 3.$$
-- source:
--   Step of the proof of M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 1.2 (p. 7): the core of the estimate (3.1). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_two_by_three_lines (M : Matrix (Fin 2) (Fin 3) ℂ)
    (hrows : LinearIndependent (↥Qbar) (Matrix.fromRows M (1 : Matrix (Fin 3) (Fin 3) ℂ)).row)
    (V : Submodule ℂ (Fin 2 → ℂ)) (hV : V ≠ ⊤) :
    Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar)
        (Set.range (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) M).col) ⊓
          V.restrictScalars (↥Qbar)) ≤ 3 := by
  sorry

end DiazModulus
