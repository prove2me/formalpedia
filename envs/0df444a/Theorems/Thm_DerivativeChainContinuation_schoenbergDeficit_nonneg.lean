-- Prove2me | Theorems.Thm_DerivativeChainContinuation_schoenbergDeficit_nonneg
-- name    : DerivativeChainContinuation.schoenbergDeficit_nonneg
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:32:57.14916+00:00
-- url     : https://prove2.me/theorems/e7b0dfc2-8b35-43f0-a99a-78caac6dfb2d
-- title:
--   Nonnegative deficit for every centered monic source
-- statement:
--   For every centered monic complex polynomial $p$ of degree $m\ge2$, $$\delta(p)=(m-2)V(p)-(m-1)V(\operatorname{monicDerivative}p)\ge0.$$ Here $V$ is the uniform squared root norm with multiplicity.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SchoenbergDeficit.lean#L64-L72

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.schoenbergDeficit_nonneg (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) (hc : p.roots.sum = 0) :
    0 ≤ schoenbergDeficit p := by sorry
