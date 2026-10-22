-- Prove2me | Theorems.Thm_AdvanceSales_Pricing_theorem_4
-- name    : AdvanceSales.Pricing.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:58.004357+00:00
-- url     : https://prove2.me/theorems/8dc2e030-ba72-4406-a73f-fa2c0eceffdb
-- title:
--   Theorem 4 — optimal price, arrival rates, and profit in four regimes
-- statement:
--   Fix the normalized late value $v$ and early-purchase penalty $k>0$. Let $W=W[-(k+1)e^{-(k+1)}]$ on the principal Lambert branch, and let $v_f>k+1$ be the second root of $f_k(v)=(1-v/(k+1))W-\ln(v-k)$. The optimal nonnegative price, its equilibrium arrival rates, and the greatest attainable profit are:
--
--   $$\begin{array}{c|c|c|c} \text{regime} & p^* & (\lambda_1,\lambda_2) & \pi^* \\ v<1 & \text{any }p\ge0 & (0,0) & 0 \\ v=1 & \text{any }p\ge0 & (0,\ln 1)=(0,0) & v-1-\ln v=0 \\ 1<v\le e^{W+k+1} & v-\frac{\ln v}{1-1/v} & (0,\ln v) & v-1-\ln v \\ e^{W+k+1}<v\le v_f & v-k-1 & (0,W+k+1) & (v-k-1)(1-e^{-(W+k+1)}) \\ v>v_f & v-k-\frac{\ln(v-k)}{1-1/(v-k)} & (\ln(v-k),0) & v-k-1-\ln(v-k) \end{array}$$
--
--   In each nonzero regime the displayed price is nonnegative, induces the stated equilibrium, earns the stated profit, and no other nonnegative price with any equilibrium earns more. When $v\le1$, every nonnegative price induces zero arrivals and the greatest profit is zero.
--
--   **Formalization Note** The printed formula for $p_2$ in case 2 is $0/0$ at $v=1$, so that boundary is stated separately: at $v=1$ every nonnegative price induces $\lambda_1=0$ and $\lambda_2=\ln 1=0$, and $\pi^*=\pi_2=0$ (the limiting price $p^*=0$ is one maximizer). The price is a maximizer, since at $v=v_f$ two distinct prices can tie. Global maximality is expressed as a greatest element of all equilibrium profits at all nonnegative prices.
-- source:
--   Glazer, Hassin, Nowik, How Advance Sales Can Reduce Profits, arXiv:1912.02869v2, p. 15, Theorem 4; p. 42, Definition 24; p. 43, Definition 26

import Mathlib
import Definitions.Def_AdvanceSales_Pricing_Setting

namespace AdvanceSales.Pricing

theorem theorem_4 (v k : ℝ) (hk : 0 < k) :
    (v < 1 →
      (∀ p x y : ℝ, 0 ≤ p → IsEq v k p x y → x = 0 ∧ y = 0) ∧
      IsGreatest (Profits v k) 0) ∧
    (v = 1 →
      (∀ p x y : ℝ, 0 ≤ p → IsEq v k p x y → x = 0 ∧ y = Real.log v) ∧
      IsGreatest (Profits v k) (pi2 v)) ∧
    (1 < v → v ≤ Real.exp (Wk k + k + 1) →
      0 ≤ p2 v ∧ IsEq v k (p2 v) 0 (Real.log v) ∧
      profit (p2 v) 0 (Real.log v) = pi2 v ∧
      IsGreatest (Profits v k) (pi2 v)) ∧
    (Real.exp (Wk k + k + 1) < v → v ≤ vf k →
      0 ≤ p3 v k ∧ IsEq v k (p3 v k) 0 (Wk k + k + 1) ∧
      profit (p3 v k) 0 (Wk k + k + 1) = pi3 v k ∧
      IsGreatest (Profits v k) (pi3 v k)) ∧
    (vf k < v →
      0 ≤ p4 v k ∧ IsEq v k (p4 v k) (Real.log (v - k)) 0 ∧
      profit (p4 v k) (Real.log (v - k)) 0 = pi4 v k ∧
      IsGreatest (Profits v k) (pi4 v k)) := by sorry

end AdvanceSales.Pricing
