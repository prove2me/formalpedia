-- Prove2me | Theorems.Thm_DetDLP_m3d_ec_compiled_bounds
-- name    : DetDLP.m3d_ec_compiled_bounds
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T00:19:33.553775+00:00
-- url     : https://prove2.me/theorems/0bbbbe43-07cf-4c18-bf86-4ccf4be05c01
-- title:
--   Compiled bounds for the EC controller
-- statement:
--   A polynomial-time EC controller transition admits a uniform simulation within polynomially scaled time and space bounds.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3D_ECFastDefs

set_option autoImplicit false
open DetDLP.M3D.Fast.ECRun OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.m3d_ec_compiled_bounds (A : Fin 9 → PrimitiveMachine) (o : ∀ j, Fin (A j).tapeCount) (J : ℕ) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (H : ℕ),
    ∀ {b : ℕ} {i y : Wd} {r : ℕ} {τ σ : ℝ}, 1 ≤ b → i.headD true = true → 1 ≤ r →
      0 ≤ τ → 0 ≤ σ → (i.length : ℝ)+r+2*σ+8 ≤ mainSpaceBound J b → τ ≤ mainTimeBound J b →
      Runs (DetDLP.M3D.Fast.NineOracleLoop.NineCall A o τ σ) r i [] y → RunsWithin D out i y (mainTimeBound H b) (mainSpaceBound H b) := by sorry
