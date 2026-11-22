-- Prove2me | Theorems.Thm_Formalism_REAL_cycleToLast_castSucc
-- name    : Formalism.REAL.cycleToLast_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:07:46.146439+00:00
-- url     : https://prove2.me/theorems/7b693ed9-b9dd-4c58-906e-3db61420783b
-- title:
--   REAL: cycle To Last cast Succ
-- statement:
--   The REAL construction uses the cycle To Last cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L220-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L220-L223

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

theorem Formalism.REAL.cycleToLast_castSucc (m : ℕ) (j : Fin (m + 1)) (k : Fin m) :
    cycleToLast m j k.castSucc = j.succAbove k := by sorry
