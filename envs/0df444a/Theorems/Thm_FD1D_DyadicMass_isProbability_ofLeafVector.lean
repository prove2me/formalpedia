-- Prove2me | Theorems.Thm_FD1D_DyadicMass_isProbability_ofLeafVector
-- name    : FD1D.DyadicMass.isProbability_ofLeafVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:25:05.682396+00:00
-- url     : https://prove2.me/theorems/8e5ee740-52fd-41ec-b17f-a7b4be572378
-- title:
--   Dyadic Mass: is Probability of Leaf Vector
-- statement:
--   The Dyadic Mass construction uses the is Probability of Leaf Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L107-L111
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L107-L111

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.DyadicMass

theorem FD1D.DyadicMass.isProbability_ofLeafVector (L : ℕ) (f : Fin (2 ^ L) → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hsum : ∑ i, f i = 1) :
    (ofLeafVector L f).IsProbability := by sorry
