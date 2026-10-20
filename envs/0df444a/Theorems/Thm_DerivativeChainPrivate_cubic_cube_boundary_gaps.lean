-- Prove2me | Theorems.Thm_DerivativeChainPrivate_cubic_cube_boundary_gaps
-- name    : DerivativeChainPrivate.cubic_cube_boundary_gaps
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T11:15:51.729986+00:00
-- url     : https://prove2.me/theorems/dec83876-84ff-4c7c-be7e-a12e079c1c6c
-- title:
--   Exact radical scalar gaps for the cubic-cube source comparison
-- statement:
--   With r=sqrt(2), alpha0=(5-3r)/14, alpha1=1/28, b0=(32-15r)/56, b1=1/7 and M=11r/448, prove alpha0>alpha1>0 and M>0, the exact positive vertical gap b1-(alpha1/alpha0)b0=3(2-r)/112, and the exact positive horizontal gap b0-b1-2M/(5/2)=(240-161r)/560. These are supporting scalar certificates; no analytic inverse graph or full cubic-cube chain is proved.
-- source:
--   Derivative-zero chains: public formalization reference, R58, DerivativeChainPrivate.cubic_cube_boundary_gaps. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.cubic_cube_boundary_gaps :
    let r := Real.sqrt 2
    let α₀ := (5 - 3 * r) / 14
    let α₁ : ℝ := 1 / 28
    let b₀ := (32 - 15 * r) / 56
    let b₁ : ℝ := 1 / 7
    let M := 11 * r / 448
    0 < α₁ ∧ α₁ < α₀ ∧ 0 < M ∧
      b₁ - (α₁ / α₀) * b₀ = 3 * (2 - r) / 112 ∧
      0 < b₁ - (α₁ / α₀) * b₀ ∧
      b₀ - b₁ - 2 * M / (5 / 2) = (240 - 161 * r) / 560 ∧
      0 < b₀ - b₁ - 2 * M / (5 / 2) := by sorry
