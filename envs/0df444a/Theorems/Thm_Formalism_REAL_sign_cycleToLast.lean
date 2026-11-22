-- Prove2me | Theorems.Thm_Formalism_REAL_sign_cycleToLast
-- name    : Formalism.REAL.sign_cycleToLast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:07:56.432357+00:00
-- url     : https://prove2.me/theorems/31e7e988-91bf-4669-b122-2955f35a7b05
-- title:
--   REAL: sign cycle To Last
-- statement:
--   The REAL construction uses the sign cycle To Last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L228-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L228-L233

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

theorem Formalism.REAL.sign_cycleToLast (m : ℕ) (j : Fin (m + 1)) :
    Equiv.Perm.sign (cycleToLast m j) = (-1) ^ (m - (j : ℕ)) := by sorry
