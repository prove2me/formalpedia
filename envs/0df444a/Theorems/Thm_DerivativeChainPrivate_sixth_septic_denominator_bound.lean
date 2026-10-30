-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_septic_denominator_bound
-- name    : DerivativeChainPrivate.sixth_septic_denominator_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:03:00.731673+00:00
-- url     : https://prove2.me/theorems/252c7938-b9b7-428e-bb88-bb1d4cf99fcc
-- title:
--   A uniformly invertible radical denominator for row 7
-- statement:
--   Use the exact fixed certificate functions $P_7,R_7,T_7$, odd polynomial $p_7$, tail $t_7$, full error $e_7=p_7+t_7$ and correction $E_7$ from the definition bundles. For every complex argument satisfying $|u|\le3/8$, $\sqrt{R_7(u)}+P_7(u)\ne0$ and $|1/(\sqrt{R_7(u)}+P_7(u))|\le5$.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthSepticSlit.lean, lines 53-70, SHA-256 9caeade69dc6966348f33c1ed7b4b8e0763c03fc4ef7d8d32d0bce3089d45704.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticAlgebra
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators

theorem DerivativeChainPrivate.sixth_septic_denominator_bound (u : ℂ) (hu : ‖u‖≤3/8) :
    Complex.sqrt (sixthSepticRadicand u)+sixthSepticPoly u≠0 ∧
      ‖(Complex.sqrt (sixthSepticRadicand u)+sixthSepticPoly u)⁻¹‖≤5 := by sorry
