-- Prove2me | Theorems.Thm_Formalism_CoboundaryTransfers_baseOfCL_qLin
-- name    : Formalism.CoboundaryTransfers.baseOfCL_qLin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:45:37.904646+00:00
-- url     : https://prove2.me/theorems/45225cc9-bb0c-4041-b94e-fa6ab9236ea3
-- title:
--   Coboundary Transfers: base Of CL q Lin
-- statement:
--   The Coboundary Transfers construction uses the base Of CL q Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/BridgeCL.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/BridgeCL.lean#L10-L13

import Definitions.Def_Formalism_CoboundaryTransfers_StatementBridge
import Definitions.Def_Formalism_WachModuleLifts_WachModuleProofs_WachModuleStatementHolds
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_BridgeCL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
open Formalism

theorem Formalism.CoboundaryTransfers.baseOfCL_qLin {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]
    (B : CL.W.Base p A) : (baseOfCL B).QLin := by sorry
