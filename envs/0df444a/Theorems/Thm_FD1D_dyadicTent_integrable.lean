-- Prove2me | Theorems.Thm_FD1D_dyadicTent_integrable
-- name    : FD1D.dyadicTent_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:25.449443+00:00
-- url     : https://prove2.me/theorems/d577211e-b9ec-4c18-928e-e5d001b09cad
-- title:
--   FD1 D: dyadic Tent integrable
-- statement:
--   The FD1 D construction uses the dyadic Tent integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L645-L651
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L645-L651

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.dyadicTent_integrable (l p : ℝ) :
    Integrable (dyadicTent l p) := by sorry
