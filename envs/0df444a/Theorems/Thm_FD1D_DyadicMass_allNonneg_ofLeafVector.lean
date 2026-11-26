-- Prove2me | Theorems.Thm_FD1D_DyadicMass_allNonneg_ofLeafVector
-- name    : FD1D.DyadicMass.allNonneg_ofLeafVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:45.798418+00:00
-- url     : https://prove2.me/theorems/859ce316-a97a-48c6-bff1-c08c8b87dc52
-- title:
--   Dyadic Mass: all Nonneg of Leaf Vector
-- statement:
--   The Dyadic Mass construction uses the all Nonneg of Leaf Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L79-L93
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L79-L93

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.DyadicMass

theorem FD1D.DyadicMass.allNonneg_ofLeafVector (L : ℕ) (f : Fin (2 ^ L) → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (ofLeafVector L f).allNonneg := by sorry
