-- Prove2me | Theorems.Thm_FD1D_transport_cost_equation_three
-- name    : FD1D.transport_cost_equation_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:33:30.778646+00:00
-- url     : https://prove2.me/theorems/68b96a40-42a7-5650-abd6-8ebf4a5d30d3
-- title:
--   FD1 D: transport cost equation three
-- statement:
--   Equation (3), with the exact constant.  `hcost` is the conditional monotone
--   quantile bound plus the deterministic within-cell error `1/n`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1838-L1878
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1838-L1878

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem FD1D.transport_cost_equation_three
    (μ : FiniteLaw Ω) (l p : ι → ℝ) (b : Ω → ι → ℝ)
    (cost : Ω → ℝ) (n a gap : ℝ)
    (_hn : 0 < n) (ha : 0 ≤ a) (hgap : 0 ≤ gap)
    (hp : ∀ i, 0 < p i)
    (hcost : ∀ ω, cost ω ≤ 1 / n +
      cdfTransportArea (haarCombination l p (b ω)))
    (hsym : ∀ i j, i ≠ j → IntervalsSeparated l p i j ∨
      μ.OddSymmetry (fun ω => b ω i * b ω j))
    (htelescope : ∑ i, p i * μ.expect (fun ω => (b ω i) ^ 2) ≤
      2 * a ^ 2 * gap) :
    μ.expect cost ≤ 1 / n + a / Real.sqrt 6 * Real.sqrt gap := by sorry
