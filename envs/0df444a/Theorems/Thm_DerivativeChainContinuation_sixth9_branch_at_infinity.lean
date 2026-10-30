-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sixth9_branch_at_infinity
-- name    : DerivativeChainContinuation.sixth9_branch_at_infinity
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:55:23.368092+00:00
-- url     : https://prove2.me/theorems/6bfadd04-5881-4898-b1d3-ec27a76baf83
-- title:
--   The validated inverse selects the first positive limiting root
-- statement:
--   Let $W:\mathbb C\to\mathbb C$ satisfy $|W(0)-P(0)|\le10^{-8}$, $G(0,W(0))=0$, and $\operatorname{Im}W(0)=0$. Put $a=\operatorname{Re}W(0)$. Then $2<a<3$, $4862-3003a+330a^2-2a^3=0$, and a is at most every positive real root of this cubic. Only these pointwise assumptions at zero are required.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9BranchPin.lean#L16-L32

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Sixth9InversePolynomial
import Definitions.Def_DerivativeChainContinuation_Sixth9PData
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.sixth9_branch_at_infinity (W : ℂ → ℂ)
    (hW : ‖W 0-sixth9P 0‖ ≤ 1/100000000)
    (hroot : sixth9G 0 (W 0)=0) (hreal : (W 0).im=0) :
    2 < (W 0).re ∧ (W 0).re < 3 ∧
      4862-3003*(W 0).re+330*(W 0).re^2-2*(W 0).re^3=0 ∧
      ∀ r : ℝ,0 < r → 4862-3003*r+330*r^2-2*r^3=0 → (W 0).re ≤ r := by sorry
