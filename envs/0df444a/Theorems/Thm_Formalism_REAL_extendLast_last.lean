-- Prove2me | Theorems.Thm_Formalism_REAL_extendLast_last
-- name    : Formalism.REAL.extendLast_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:48.067917+00:00
-- url     : https://prove2.me/theorems/8d147fdc-6278-4cf8-9e82-2980173697e3
-- title:
--   REAL: extend Last last
-- statement:
--   The REAL construction uses the extend Last last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L242-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L242-L243

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

theorem Formalism.REAL.extendLast_last {m : ℕ} (τ : Equiv.Perm (Fin m)) : extendLast τ (Fin.last m) = Fin.last m := by sorry
