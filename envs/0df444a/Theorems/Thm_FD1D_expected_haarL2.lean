-- Prove2me | Theorems.Thm_FD1D_expected_haarL2
-- name    : FD1D.expected_haarL2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:50.396006+00:00
-- url     : https://prove2.me/theorems/81096f66-487d-4842-8f5e-2ba77ba38171
-- title:
--   FD1 D: expected haar L2
-- statement:
--   Expected Parseval identity for integrated Haar functions.  For unequal
--   nodes, either their interiors are disjoint or a tree child swap makes the
--   coefficient product odd.  Thus every cross term vanishes.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1372-L1404
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1372-L1404

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem FD1D.expected_haarL2 (μ : FiniteLaw Ω) (l p : ι → ℝ)
    (b : Ω → ι → ℝ) (hp : ∀ i, 0 < p i)
    (hsym : ∀ i j, i ≠ j → IntervalsSeparated l p i j ∨
      μ.OddSymmetry (fun ω => b ω i * b ω j)) :
    μ.expect (fun ω => haarL2 l p (b ω)) =
      (1 / 12) * ∑ i, p i * μ.expect (fun ω => (b ω i) ^ 2) := by sorry
