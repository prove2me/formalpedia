-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_octic_coefficient_bounds
-- name    : DerivativeChainPrivate.sixth_octic_coefficient_bounds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:18:21.778518+00:00
-- url     : https://prove2.me/theorems/8a2df6d8-23fb-40d5-a958-b86a1aa82e78
-- title:
--   Exact majorants for every eighth-row expansion coefficient
-- statement:
--   The leading eighth-row coefficient satisfies $38/1000<a_0<39/1000$, the absolute rational-tail coefficient satisfies $|c_8|\le4213$, and every one of the nineteen expansion coefficients obeys $|a_i|\le d_i$ with its fixed rational majorant $d_i$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthOcticAlgebra.lean, lines 53-67, SHA-256 c39ecae5972d766d97cc7a245d026306777e68e7c5abc4109799c04458139db6.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
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

theorem DerivativeChainPrivate.sixth_octic_coefficient_bounds :
    (38/1000:ℝ)<sixthOcticExpansionCoeffs 0 ∧ sixthOcticExpansionCoeffs 0<39/1000 ∧
      |sixthOcticRationalTailCoeff| ≤ 4213 ∧
      ∀ i : Fin 19, |sixthOcticExpansionCoeffs i| ≤ sixthOcticExpansionBounds i := by sorry
