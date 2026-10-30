-- Prove2me | Theorems.Thm_DerivativeChainPrivate_derivative_real_supporting_parent
-- name    : DerivativeChainPrivate.derivative_real_supporting_parent
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:16:08.368867+00:00
-- url     : https://prove2.me/theorems/fc789c53-8980-413e-84e7-a03b133bfb01
-- title:
--   A derivative root has a source root to its right
-- statement:
--   For any nonconstant $p\in\mathbb C[X]$ and $w\in\mathbb C$ with $p^{\prime}(w)=0$, there is $z\in\mathbb C$ with $p(z)=0$ and $\operatorname{Re}w\le\operatorname{Re}z$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L343-L367

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.derivative_real_supporting_parent (p : Polynomial ℂ) (hp : 0 < p.natDegree)
    (w : ℂ) (hw : p.derivative.eval w = 0) :
    ∃ z : ℂ, p.eval z = 0 ∧ w.re ≤ z.re := by sorry
