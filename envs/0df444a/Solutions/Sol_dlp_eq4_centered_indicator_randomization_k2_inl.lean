-- Prove2me | solution 1 for dlp_eq4_centered_indicator_randomization_k2_inl
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T17:07:15.370478+00:00
-- url     : https://prove2.me/submissions/e0e60671-a3f2-4119-b078-7ec05a164f7e

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_dlp_sigma_randomization
import Theorems.Thm_dlp_eq4_four_corner_randomization_k2
open MatrixCompletion
open scoped BigOperators Classical

theorem solution
    {n1 n2 : Nat}
    (Omega1 Omega2 : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (w1 w2 : Fin n1 × Fin n2)
    (sigma1 sigma2 : ℝ) (hs1 : sigma1 = 1 ∨ sigma1 = -1) (hs2 : sigma2 = 1 ∨ sigma2 = -1)
    (l1 l2 : Fin 2) :
    (4 : ℝ) *
        (centeredIndicator (if dlpCopyPerm sigma1 l1 = 0 then Omega1 else Omega2) p w1.1 w1.2 *
          centeredIndicator (if dlpCopyPerm sigma2 l2 = 0 then Omega1 else Omega2) p w2.1 w2.2)
      = ∑ j1 : Fin 2, ∑ j2 : Fin 2,
          ((1 + dlpCornerSign j1 l1 * sigma1) * (1 + dlpCornerSign j2 l2 * sigma2)) *
            (centeredIndicator (if j1 = 0 then Omega1 else Omega2) p w1.1 w1.2 *
              centeredIndicator (if j2 = 0 then Omega1 else Omega2) p w2.1 w2.2) := by
  have h := dlp_eq4_four_corner_randomization_k2 (V := ℝ) sigma1 sigma2 hs1 hs2 l1 l2
    (fun j1 j2 =>
      centeredIndicator (if j1 = 0 then Omega1 else Omega2) p w1.1 w1.2 *
        centeredIndicator (if j2 = 0 then Omega1 else Omega2) p w2.1 w2.2)
  simpa only [smul_eq_mul] using h
