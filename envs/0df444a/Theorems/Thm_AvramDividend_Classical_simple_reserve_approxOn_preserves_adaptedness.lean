-- Prove2me | Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_preserves_adaptedness
-- name    : AvramDividend.Classical.simple_reserve_approxOn_preserves_adaptedness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:06:47.25168+00:00
-- url     : https://prove2.me/theorems/c7156546-0439-4a7d-b4dd-9c7ecd503276
-- title:
--   Simple-function quantisation preserves measurability in any source filtration sigma-algebra
-- statement:
--   Let Z be a real-valued function measurable both in an ambient measurable space and in another source measurable space representing information at an observation time. For any measurable target set and base point used in Mathlib SimpleFunc.approxOn, the resulting finite-valued quantisation is measurable in the source measurable space as well. Factor the approximating simple function through Z using the exact pinned Mathlib declaration SimpleFunc.approxOn_comp, apply measurability of the quantisation of the identity, and rewrite with SimpleFunc.coe_comp. This supports adapted simple reserve approximations for stochastic Markov identities.
-- source:
--   Pinned declaration oracle confirms SimpleFunc.approxOn_comp and SimpleFunc.coe_comp at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. No dependence on a pending Prove2Me theorem.

import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

open MeasureTheory

theorem AvramDividend.Classical.simple_reserve_approxOn_preserves_adaptedness
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (m' : MeasurableSpace Ω)
    (Z : Ω → ℝ)
    (hZ : Measurable[m'] Z) (hZm : Measurable Z)
    (s : Set ℝ) (y₀ : ℝ) (hy₀ : y₀ ∈ s) (n : ℕ) :
    Measurable[m'] (fun ω =>
      (SimpleFunc.approxOn Z hZm s y₀ hy₀ n) ω) := by sorry
