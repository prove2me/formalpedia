-- Prove2me | Theorems.Thm_FD1D_DyadicMass_nodeCoefficient_eq_childMass_sub
-- name    : FD1D.DyadicMass.nodeCoefficient_eq_childMass_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:28:58.153324+00:00
-- url     : https://prove2.me/theorems/fdde7fbb-83d7-5664-a216-ca2db143176e
-- title:
--   Dyadic Mass: node Coefficient eq child Mass sub
-- statement:
--   The Dyadic Mass construction uses the node Coefficient eq child Mass sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L945-L949
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L945-L949

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.DyadicMass

theorem FD1D.DyadicMass.nodeCoefficient_eq_childMass_sub {L : ℕ} (q : DyadicMass L)
    (v : CompleteHaarNode L) :
    q.nodeCoefficient v =
      (q.nodeChildMasses v).1 - (q.nodeChildMasses v).2 := by sorry
