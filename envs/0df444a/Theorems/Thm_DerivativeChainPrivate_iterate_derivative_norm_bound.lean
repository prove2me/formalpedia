-- Prove2me | Theorems.Thm_DerivativeChainPrivate_iterate_derivative_norm_bound
-- name    : DerivativeChainPrivate.iterate_derivative_norm_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:49:06.813369+00:00
-- url     : https://prove2.me/theorems/124fccfc-3f1e-48de-bc53-069f32a29178
-- title:
--   Root bounds persist through nonconstant derivative rows
-- statement:
--   Let $p\in\mathbb C[X]$, $k<\deg p$, and $M\in\mathbb R$. If every root of $p$ has modulus at most $M$, every root of $p^{(k)}$ also has modulus at most $M$. The restriction $k<\deg p$ excludes the identically zero derivative rows.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L1984-L1998

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.iterate_derivative_norm_bound (p : Polynomial ℂ) (k : ℕ) (hk : k < p.natDegree)
    (M : ℝ) (hbound : ∀ z, p.eval z = 0 → ‖z‖ ≤ M) (z : ℂ)
    (hz : (derivative^[k] p).eval z = 0) : ‖z‖ ≤ M := by sorry
