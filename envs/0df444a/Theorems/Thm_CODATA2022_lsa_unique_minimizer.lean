-- Prove2me | Theorems.Thm_CODATA2022_lsa_unique_minimizer
-- name    : CODATA2022.lsa_unique_minimizer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:21:58.249621+00:00
-- url     : https://prove2.me/theorems/791bf826-9613-4851-9d41-db118f32c5b9
-- title:
--   Unique minimizer $\hat x = (A^{\mathsf T}WA)^{-1}A^{\mathsf T}Wz$
-- statement:
--   When $A^{\mathsf T}WA$ is invertible - the usual non-degeneracy condition of an
--   adjustment, equivalent for positive definite $W$ to the input data determining all $M$
--   adjusted constants - the least-squares problem has exactly one solution, and it is given in
--   closed form:
--
--   $$\hat x \;=\; \bigl(A^{\mathsf T}WA\bigr)^{-1}A^{\mathsf T}Wz .$$
--
--   The statement has two halves: this vector minimizes $\chi^2$, and any minimizer equals it.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Sec. XIV.A: the 2022 adjustment determines $M=79$ adjusted constants from $N=133$ input data by least squares.

import Mathlib
import Definitions.Def_CODATA2022_least_squares
open Matrix

namespace CODATA2022
theorem lsa_unique_minimizer {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (hW : W.PosDef) (z : Fin N → ℝ)
    (hinv : IsUnit (Aᵀ * W * A).det) :
    (∀ x : Fin M → ℝ,
        chiSquare A W z ((Aᵀ * W * A)⁻¹.mulVec ((Aᵀ * W).mulVec z)) ≤ chiSquare A W z x) ∧
      ∀ y : Fin M → ℝ, (∀ x : Fin M → ℝ, chiSquare A W z y ≤ chiSquare A W z x) →
        y = (Aᵀ * W * A)⁻¹.mulVec ((Aᵀ * W).mulVec z) := by sorry
end CODATA2022
