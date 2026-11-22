-- Prove2me | Theorems.Thm_Auto_dirichletKernel_mul_sin
-- name    : Auto.dirichletKernel_mul_sin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:59.2593+00:00
-- url     : https://prove2.me/theorems/a7e4a952-f69c-4727-ac3a-bd66bfc3ff50
-- title:
--   Auto: dirichlet Kernel mul sin
-- statement:
--   The closed form `D_N(s) sin(πs) = sin((2N+1)πs)` of the Dirichlet kernel.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L850-L893
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L850-L893

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real

theorem Auto.dirichletKernel_mul_sin (N : ℕ) (s : ℝ) :
    dirichletKernel N s * (Real.sin (π * s) : ℂ) = (Real.sin ((2 * N + 1) * π * s) : ℂ) := by sorry
