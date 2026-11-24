-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelGen_levelIdx
-- name    : Formalism.MainNotions.BridgeLevelGen.levelIdx
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:59:03.255579+00:00
-- url     : https://prove2.me/theorems/57da3f20-6b64-4d84-baba-c8c76082bd68
-- title:
--   Bridge Level Gen: level Idx
-- statement:
--   The Bridge Level Gen construction uses the level Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGen.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGen.lean#L105-L107

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB
import Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLatticeOfRel
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGen
open MeasureTheory NumberField Formalism.MainNotions.S Formalism.MainNotions.BridgeLevelIdx
open scoped ENNReal TensorProduct

theorem Formalism.MainNotions.BridgeLevelGen.levelIdx (I : AutInst) (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {g : ℕ} (hg : 1 ≤ g) :
    μf I.Kset ≤ ((g ^ (2 * I.n ^ 2 * I.f) : ℕ) : ℝ≥0∞) * μf (I.Kg g) := by sorry
