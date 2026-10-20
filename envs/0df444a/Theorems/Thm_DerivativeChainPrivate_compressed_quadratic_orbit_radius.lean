-- Prove2me | Theorems.Thm_DerivativeChainPrivate_compressed_quadratic_orbit_radius
-- name    : DerivativeChainPrivate.compressed_quadratic_orbit_radius
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T05:03:46.122488+00:00
-- url     : https://prove2.me/theorems/c5260c16-ac9a-41af-a88d-bdb20cd8aafa
-- title:
--   A nonreal real-quadratic compressed orbit has one radius
-- statement:
--   Let A,B be real with A squared less than 4B. For every natural d and complex w satisfying (w to the d) squared plus A times w to the d plus B equals zero, the norm of w to the power 2d equals B. All roots in the compressed quadratic orbit therefore have the same radius. The theorem retains its literal d=0 case; it asserts no chain bound.
-- source:
--   Derivative-zero chains: public formalization reference, R47, DerivativeChainPrivate.compressed_quadratic_orbit_radius. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.compressed_quadratic_orbit_radius (A B : ℝ) (hdisc : A ^ 2 < 4 * B)
    (d : ℕ) (w : ℂ)
    (hroot : (w ^ d) ^ 2 + (A : ℂ) * w ^ d + (B : ℂ) = 0) :
    ‖w‖ ^ (2 * d) = B := by sorry
