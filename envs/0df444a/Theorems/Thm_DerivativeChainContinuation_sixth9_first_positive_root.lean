-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sixth9_first_positive_root
-- name    : DerivativeChainContinuation.sixth9_first_positive_root
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:53:31.359076+00:00
-- url     : https://prove2.me/theorems/4c9ba22e-02fe-4e82-9768-71562f35235a
-- title:
--   A root in (2,3) is the least positive inverse root
-- statement:
--   Put $H(x)=4862-3003x+330x^2-2x^3$. For real $a\in(2,3)$ with $H(a)=0$ and every real $r>0$ with $H(r)=0$, one has $a\le r$. The root a is assumed in this lemma.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9BranchPin.lean#L5-L14

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.sixth9_first_positive_root (a : ℝ) (ha : 2 < a ∧ a < 3)
    (he : 4862-3003*a+330*a^2-2*a^3=0) (r : ℝ) (hr : 0 < r)
    (hre : 4862-3003*r+330*r^2-2*r^3=0) : a ≤ r := by sorry
