-- Prove2me | Theorems.Thm_Formalism_CoboundaryTransfers_wach_api
-- name    : Formalism.CoboundaryTransfers.wach_api
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:23:11.381243+00:00
-- url     : https://prove2.me/theorems/573a21d5-1095-4b4d-aa5c-ef72d4847ad5
-- title:
--   Coboundary Transfers: wach api
-- statement:
--   The Coboundary Transfers construction uses the wach api property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/WachBridges.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/WachBridges.lean#L16-L21

import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_GammaStableOfGammaQUnitHolds
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DiffOneSmulOfTower
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_BridgeCL
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_BridgeLIFT
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DepthPageFirstZetaFactorEqPrimePower
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_Transfer
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_WachLatticeNonemptyGamma
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_IntegralWachDefinitions
import Definitions.Def_Formalism_CoboundaryTransfers_WachBridges
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

theorem Formalism.CoboundaryTransfers.wach_api : Complex ∧ Submods ∧ CocZf ∧ HomMaps ∧ GammaQNOf ∧ DiagramChase₂ ∧ CoboundaryTransfer ∧
    GradedStep ∧ GammaOnto ∧ ColBound ∧ LiftHf ∧ Mono ∧ IntDefs ∧ NonemptyQ ∧ NonemptyU ∧
    NonemptyG := by sorry
