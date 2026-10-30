-- Prove2me | Theorems.Thm_DerivativeChainContinuation_arbitrary_source_deficit_inequalities
-- name    : DerivativeChainContinuation.arbitrary_source_deficit_inequalities
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:03:24.542961+00:00
-- url     : https://prove2.me/theorems/c98db163-3582-4f82-b877-25a5004acb1b
-- title:
--   Deficit inequalities after centering an arbitrary monic source
-- statement:
--   For any monic complex polynomial $p$ of degree at least two, translate by its actual root centroid to obtain $p_c$. Then $$0\le\delta(p_c),\qquad \frac{\det\Sigma(p_c)}{2R(p_c)^2}\le\delta(p_c).$$ No centering hypothesis is imposed on the original source.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/DeficitCentered.lean#L7-L15

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainContinuation_DeficitInequalities
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.arbitrary_source_deficit_inequalities (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) :
    0 ≤ schoenbergDeficit (centeredSource p) ∧
      (rootCovariance (centeredSource p)).det /
        (2*(rootRadius (centeredSource p))^2) ≤ schoenbergDeficit (centeredSource p) := by sorry
