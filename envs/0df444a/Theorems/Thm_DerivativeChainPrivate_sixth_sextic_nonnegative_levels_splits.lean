-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_sextic_nonnegative_levels_splits
-- name    : DerivativeChainPrivate.sixth_sextic_nonnegative_levels_splits
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:53:45.44291+00:00
-- url     : https://prove2.me/theorems/64916916-d365-4b79-8e70-e906b503325f
-- title:
--   Every nonnegative level polynomial splits over the reals
-- statement:
--   For every real $t\ge0$, $211302X^3-417690X^2+(169065-211302t)X+24565$ splits over $\mathbb R$.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/join56/SixthSexticMeasure.lean, lines 8-51, SHA-256 f19a7e37af0a4cf3b58735dffb2bd056564dcad32770885ad8b580768e3b3091.

import Mathlib
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

theorem DerivativeChainPrivate.sixth_sextic_nonnegative_levels_splits (t : ℝ) (ht : 0 ≤ t) :
    (211302*X^3 + (-417690)*X^2 + C (169065-211302*t)*X + 24565 : Polynomial ℝ).Splits := by sorry
