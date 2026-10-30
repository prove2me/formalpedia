-- Prove2me | Theorems.Thm_DerivativeChainContinuation_deficit_determinant_inequality
-- name    : DerivativeChainContinuation.deficit_determinant_inequality
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:57:55.256111+00:00
-- url     : https://prove2.me/theorems/299b2180-641a-4abc-ab00-1eca93715e63
-- title:
--   Intrinsic root-radius lower bound for the deficit
-- statement:
--   For every centered monic complex polynomial $p$ of degree at least two, let $R$ be its largest root norm and $\Sigma$ its real root covariance. Then $$\frac{\det\Sigma}{2R^2}\le\delta(p).$$ Division is totalized; the zero-radius case is included.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/DeficitInequalities.lean#L42-L45

import Mathlib
import Definitions.Def_DerivativeChainContinuation_DeficitInequalities
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.deficit_determinant_inequality (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) (hc : p.roots.sum = 0) :
    (rootCovariance p).det/(2*(rootRadius p)^2) ≤ schoenbergDeficit p := by sorry
