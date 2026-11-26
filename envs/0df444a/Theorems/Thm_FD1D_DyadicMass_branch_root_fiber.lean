-- Prove2me | Theorems.Thm_FD1D_DyadicMass_branch_root_fiber
-- name    : FD1D.DyadicMass.branch_root_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:22.651971+00:00
-- url     : https://prove2.me/theorems/f60dccbe-aa12-597f-a610-60de8277417a
-- title:
--   Dyadic Mass: branch root fiber
-- statement:
--   The Dyadic Mass construction uses the branch root fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1245-L1267
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1245-L1267

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass

theorem FD1D.DyadicMass.branch_root_fiber {L : ℕ} (l r : DyadicMass L) (z : ℝ) :
    (∑ y : Fin (2 ^ (0 : Fin (L + 1)).val),
      (branch l r).nodeCoefficient ⟨(0 : Fin (L + 1)), y⟩ *
        dyadicTent (haarNodeLeft ⟨(0 : Fin (L + 1)), y⟩)
          (haarNodeWidth ⟨(0 : Fin (L + 1)), y⟩) z) =
      (l.total - r.total) * dyadicTent 0 1 z := by sorry
