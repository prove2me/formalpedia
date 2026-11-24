-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_levelIdx_holds
-- name    : Formalism.MainNotions.BridgeLevelIdx.levelIdx_holds
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:42:26.072418+00:00
-- url     : https://prove2.me/theorems/8114bd2b-eee4-4bf1-a215-2a7f0c7ab01f
-- title:
--   Bridge Level Idx: level Idx holds
-- statement:
--   The Bridge Level Idx construction uses the level Idx holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L104-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L104-L124

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelIdx
open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct
variable (I : AutInst)
variable {I}

theorem Formalism.MainNotions.BridgeLevelIdx.levelIdx_holds (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {g : ℕ} (hg : 1 ≤ g) (hG : LevelGen I g) :
    μf I.Kset ≤ ((g ^ (2 * I.n ^ 2 * I.f) : ℕ) : ℝ≥0∞) * μf (I.Kg g) := by sorry
