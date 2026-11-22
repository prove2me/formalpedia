-- Prove2me | Theorems.Thm_Formalism_REAL_extendLast_castSucc
-- name    : Formalism.REAL.extendLast_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:09.5358+00:00
-- url     : https://prove2.me/theorems/9fa0c19e-8836-49c0-afab-5017664df63d
-- title:
--   REAL: extend Last cast Succ
-- statement:
--   The REAL construction uses the extend Last cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L238-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L238-L240

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

theorem Formalism.REAL.extendLast_castSucc {m : ℕ} (τ : Equiv.Perm (Fin m)) (k : Fin m) :
    extendLast τ k.castSucc = (τ k).castSucc := by sorry
