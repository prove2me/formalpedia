-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_octic_radicand_im_nonzero
-- name    : DerivativeChainPrivate.sixth_octic_radicand_im_nonzero
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:23:56.646606+00:00
-- url     : https://prove2.me/theorems/c944b5be-95a8-4b12-872f-6071cded6601
-- title:
--   The eighth-row radicand is nonreal at nonreal disk arguments
-- statement:
--   If complex $|u|\le3/10$ and $\Im u\ne0$, then $\Im R_8(u)\ne0$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthOcticSlit.lean, lines 23-65, SHA-256 67aa5d06279bc377e130819f0739f653fc81e4fafeb8c7801b850a9493fb8e62.

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

theorem DerivativeChainPrivate.sixth_octic_radicand_im_nonzero (u : ℂ) (hu : ‖u‖≤3/10) (hi : u.im≠0) :
    (sixthOcticRadicand u).im≠0 := by sorry
