-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_septic_tail_differentiableAt
-- name    : DerivativeChainPrivate.sixth_septic_tail_differentiableAt
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:05:18.622222+00:00
-- url     : https://prove2.me/theorems/7ba111d3-2d38-4989-bbb7-17b10e5475fa
-- title:
--   Complex differentiability of the tail for row 7
-- statement:
--   Use the exact fixed certificate functions $P_7,R_7,T_7$, odd polynomial $p_7$, tail $t_7$, full error $e_7=p_7+t_7$ and correction $E_7$ from the definition bundles. For every complex argument satisfying $|w|\le3/5$, $t_7$ is complex differentiable at $w$.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthSepticTail.lean, lines 27-44, SHA-256 8598bb9e35a3ea85c33363553959b61fa1ad14eb9a4318b0457449e869f1aba9.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticTail
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

theorem DerivativeChainPrivate.sixth_septic_tail_differentiableAt (w : ℂ) (hw : ‖w‖≤3/5) :
    DifferentiableAt ℂ sixthSepticTail w := by sorry
