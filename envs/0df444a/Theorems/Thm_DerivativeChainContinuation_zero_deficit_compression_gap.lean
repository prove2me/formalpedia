-- Prove2me | Theorems.Thm_DerivativeChainContinuation_zero_deficit_compression_gap
-- name    : DerivativeChainContinuation.zero_deficit_compression_gap
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:34:32.248478+00:00
-- url     : https://prove2.me/theorems/2901c889-e263-4506-9635-ca18acd44339
-- title:
--   Zero centered deficit forces zero compression gap at every query center
-- statement:
--   For any list of at least two complex source roots, suppose the Schoenberg deficit after translation by the actual centroid is zero. At every query center $z$ and every positive squared scale $t$, $$\Gamma(a-z,t)=0.$$ Repeated roots and arbitrary source centroid are allowed.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AllScaleArbitrarySource.lean#L31-L36

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AllScaleCompression
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.zero_deficit_compression_gap (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℂ)
    (hzero : schoenbergDeficit (∏ i,(X-C (a i-complexCentroid a)))=0)
    (z : ℂ) (t : ℝ) (ht : 0 < t) : scaleCompressionGap (fun i => a i-z) t=0 := by sorry
