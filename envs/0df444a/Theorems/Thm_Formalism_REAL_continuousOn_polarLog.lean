-- Prove2me | Theorems.Thm_Formalism_REAL_continuousOn_polarLog
-- name    : Formalism.REAL.continuousOn_polarLog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:25.570498+00:00
-- url     : https://prove2.me/theorems/328bf0f0-bc68-42af-a7f9-ecf365450219
-- title:
--   REAL: continuous On polar Log
-- statement:
--   The REAL construction uses the continuous On polar Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IndefiniteUnitaryPreservesForm.lean#L271-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IndefiniteUnitaryPreservesForm.lean#L271-L278

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}

theorem Formalism.REAL.continuousOn_polarLog (ε : Fin n → Bool) : ContinuousOn (polarLog (n := n)) {g | inUJ ε g} := by sorry
