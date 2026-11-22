-- Prove2me | Theorems.Thm_Formalism_REAL_cycleToLast_last
-- name    : Formalism.REAL.cycleToLast_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:01:55.394798+00:00
-- url     : https://prove2.me/theorems/f473a497-b4c8-4eeb-b63f-03f6ab20d0df
-- title:
--   REAL: cycle To Last last
-- statement:
--   The REAL construction uses the cycle To Last last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L225-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L225-L226

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

theorem Formalism.REAL.cycleToLast_last (m : ℕ) (j : Fin (m + 1)) : cycleToLast m j (Fin.last m) = j := by sorry
