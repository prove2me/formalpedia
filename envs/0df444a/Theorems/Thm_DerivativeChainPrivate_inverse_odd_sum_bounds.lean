-- Prove2me | Theorems.Thm_DerivativeChainPrivate_inverse_odd_sum_bounds
-- name    : DerivativeChainPrivate.inverse_odd_sum_bounds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:40:08.400838+00:00
-- url     : https://prove2.me/theorems/5added28-8911-4fed-a170-535770dcc56d
-- title:
--   Weighted bounds for every finite real odd reciprocal-power sum
-- statement:
--   For finite real coefficients $c_i$, natural $k_i$, real $T>0$, and $z=x+iy$ with $x,y>0$, $x^2\ge T$, put $E=\sum_i c_i z^{-2k_i-1}$. Then $|\Re E/x|\le\sum_i|c_i|T^{-k_i-1}$ and $|(3\Re E/x-\Im E/y)/2|\le\sum_i|c_i|(k_i+2)T^{-k_i-1}$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/InversePowerCoordinates.lean, lines 91-129, SHA-256 0ba4ed1f230fc8ee6c4a7f6f64180cc1c8fa9bd50285e1f1e157b75ef4c79286.

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

theorem DerivativeChainPrivate.inverse_odd_sum_bounds {n : ℕ} (c : Fin n → ℝ) (k : Fin n → ℕ)
    (T : ℝ) (hT : 0<T) (z : ℂ) (hx : 0<z.re) (hy : 0<z.im) (hX : T≤z.re^2) :
    let E:=∑ i,(c i:ℂ)*(z⁻¹)^(2*k i+1)
    |E.re/z.re|≤∑ i,|c i| *(T⁻¹)^(k i+1) ∧
      |(3*(E.re/z.re)-E.im/z.im)/2|≤∑ i,|c i| *(k i+2:ℝ)*(T⁻¹)^(k i+1) := by sorry
