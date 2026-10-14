-- Prove2me | Theorems.Thm_Apery_det_basis_change
-- name    : Apery.det_basis_change
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T18:43:31.367175+00:00
-- url     : https://prove2.me/theorems/b74b5da6-6cdf-4c95-8cd3-a1b612546b72
-- title:
--   Change of basis in the Hankel determinant: $\det(\mu_X(D_N^6 E_a E_b)) = \det(C)^2 \Delta_K$
-- statement:
--   For $K = 40n$, $N = 3n$, $h = 37n$ and polynomials $E_a \in \mathbb{Q}[X]$ of degree $< h$ ($a < h$), the Hankel matrix $\big(\mu_X(D_N^6 E_a E_b)\big)_{a,b}$ factors as $\det = \det(C)^2 \, \Delta_K$, where $C_{ak} = \mathrm{coeff}_k(E_a)$ is the coefficient matrix of the basis $E$ and $\Delta_K = \det G_K$ is the Hankel determinant. This is `det_basis_change` of `Apery/Arith/BasisChange.lean`: the change-of-basis step that lets the small-prime and $T$-key bounds work in the monomial basis, combined with the partial-fraction expansion `partial_fractions` of `μ_X(P/D_K)$ (`Apery/PartialFractions.lean`, `Apery/Degree.lean`). **Formalization Note** `μX`, `D`, `Δ`, `G` are the platform definitions of `Definitions.Def_Zeta5_SourceConstruction`; the coefficient matrix is written out explicitly since it is a local definition of the same file.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/BasisChange.lean#L1-L100 (+ Apery/Degree.lean, Apery/PartialFractions.lean)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction

open Polynomial Matrix Finset

namespace Apery

theorem det_basis_change (n : ℕ) (E : Fin (37 * n) → ℚ[X])
    (hE : ∀ a, (E a).natDegree < 37 * n) :
    (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)).det =
      C ((Matrix.of (fun a k => (E a).coeff k : Fin (37 * n) → Fin (37 * n) → ℚ)).det ^ 2) * Δ n := by
  sorry

end Apery
