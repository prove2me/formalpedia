-- Prove2me | Theorems.Thm_FD1D_DyadicMass_branch_succ_fiber
-- name    : FD1D.DyadicMass.branch_succ_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:11.844992+00:00
-- url     : https://prove2.me/theorems/3594f7e7-4224-459c-a93b-9299b0630498
-- title:
--   Dyadic Mass: branch succ fiber
-- statement:
--   The Dyadic Mass construction uses the branch succ fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1092-L1121
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1092-L1121

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass

theorem FD1D.DyadicMass.branch_succ_fiber {L : ℕ} (l r : DyadicMass L) (d : Fin L)
    (z : ℝ) :
    (∑ y : Fin (2 ^ d.succ.val),
      (branch l r).nodeCoefficient ⟨d.succ, y⟩ *
        dyadicTent (haarNodeLeft ⟨d.succ, y⟩)
          (haarNodeWidth ⟨d.succ, y⟩) z) =
      (∑ y : Fin (2 ^ d.val),
        l.nodeCoefficient ⟨d, y⟩ *
          dyadicTent (haarNodeLeft (leftNode ⟨d, y⟩))
            (haarNodeWidth (leftNode ⟨d, y⟩)) z) +
      ∑ y : Fin (2 ^ d.val),
        r.nodeCoefficient ⟨d, y⟩ *
          dyadicTent (haarNodeLeft (rightNode ⟨d, y⟩))
            (haarNodeWidth (rightNode ⟨d, y⟩)) z := by sorry
