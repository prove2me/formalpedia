-- Prove2me | Theorems.Thm_DynOpaque_TwoPeriod_benchmark_transparent
-- name    : DynOpaque.TwoPeriod.benchmark_transparent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:24.191761+00:00
-- url     : https://prove2.me/theorems/fe2d9d00-2075-43f4-892d-36fd864300eb
-- title:
--   §3.3 Benchmark, p. 11 — transparent selling earns at most 2·max{vH − cH, vL − cL}, attained at pH = vH or pL = vL
-- statement:
--   Assume $v_H>v_L$, $c_H>c_L$, $0\le\alpha\le1$, $c_L\le v_L$. A transparent policy sells one version $m\in\{H,L\}$ in both periods at prices $q_1,q_2$; customers buy in period $t$ iff $q_t\le v_m$. Then:
--
--   1. every transparent policy earns at most
--   $$
--   2\max\{v_H-c_H,\ v_L-c_L\};
--   $$
--   2. selling $H$ at price $v_H$ in both periods earns $2(v_H-c_H)$;
--   3. selling $L$ at price $v_L$ in both periods earns $2(v_L-c_L)$.
--
--   Hence the optimal transparent policy sells $H$ when $v_H-c_H\ge v_L-c_L$ and $L$ when $v_L-c_L\ge v_H-c_H$. This is the benchmark against which the probabilistic selling policy is compared in Proposition 1.
--
--   **Formalization Note** The bound in item 1 uses $c_L\le v_L$ (so the bound is nonnegative, covering prices at which nobody buys).
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, p. 11, §3.3 Benchmark

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaque.TwoPeriod

/-- §3.3 Benchmark, p. 11: every transparent policy earns at most
`2 max{vH − cH, vL − cL}`; selling `H` at `vH` in both periods earns `2(vH − cH)`, selling `L` at
`vL` in both periods earns `2(vL − cL)`. -/
theorem benchmark_transparent (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    (∀ (m : Version) (q₁ q₂ : ℝ),
      transparentProfit vH vL cH cL m q₁ q₂ ≤ 2 * max (vH - cH) (vL - cL)) ∧
    transparentProfit vH vL cH cL Version.H vH vH = 2 * (vH - cH) ∧
    transparentProfit vH vL cH cL Version.L vL vL = 2 * (vL - cL) := by sorry

end DynOpaque.TwoPeriod
