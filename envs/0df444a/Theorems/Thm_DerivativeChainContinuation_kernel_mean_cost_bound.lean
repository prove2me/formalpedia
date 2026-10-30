-- Prove2me | Theorems.Thm_DerivativeChainContinuation_kernel_mean_cost_bound
-- name    : DerivativeChainContinuation.kernel_mean_cost_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:35:29.426568+00:00
-- url     : https://prove2.me/theorems/5081fe99-93ab-43c7-9adc-7221044354cf
-- title:
--   Mean endpoint costs propagate through a finite kernel
-- statement:
--   For nonnegative finite weights $w_i$, a nonnegative row-stochastic kernel $K_{ia}$, and real endpoint costs $f_i,g_a$, suppose $g_a\le f_i+|y_a-x_i|$ for every pair. With $\widetilde w_a=\sum_iw_iK_{ia}$ and $c_i=\sum_aK_{ia}|y_a-x_i|$, $$\sum_a\widetilde w_a g_a\le\sum_iw_if_i+\sum_iw_ic_i.$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/KernelCostTransport.lean#L6-L23

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.kernel_mean_cost_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (K : ι → κ → ℝ) (x : ι → ℂ) (y : κ → ℂ)
    (f : ι → ℝ) (g : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hK : ∀ i a, 0 ≤ K i a) (hKs : ∀ i, ∑ a, K i a=1)
    (hcost : ∀ i a, g a ≤ f i+‖y a-x i‖) :
    (∑ a, (∑ i, w i*K i a)*g a) ≤ (∑ i, w i*f i)+(∑ i, w i*kernelCost K x y i) := by sorry
