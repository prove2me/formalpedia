-- Prove2me | Theorems.Thm_Formalism_REAL_lastColumnSplit_bijective
-- name    : Formalism.REAL.lastColumnSplit_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:45.402665+00:00
-- url     : https://prove2.me/theorems/c0abbb9e-b58b-44f2-bd0c-b8c3b7cb4479
-- title:
--   REAL: last Column Split bijective
-- statement:
--   The REAL construction uses the last Column Split bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L253-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L253-L268

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.lastColumnSplit_bijective (m : ℕ) : Function.Bijective (lastColumnSplit m) := by sorry
