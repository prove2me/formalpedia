-- Prove2me | Theorems.Thm_Formalism_L2_G_isUnit_det_gram0
-- name    : Formalism.L2.G.isUnit_det_gram0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:29:00.023186+00:00
-- url     : https://prove2.me/theorems/a06c564a-4ed4-4508-8935-a4f3fa0ae5aa
-- title:
--   G: is Unit det gram0
-- statement:
--   The G construction uses the is Unit det gram0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelGatherings/GramDetIsUnit.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelGatherings/GramDetIsUnit.lean#L11-L30

import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelGatherings_GramDetIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions NumberField Formalism.UG
open Formalism Formalism.L2 Formalism.L2.G
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem Formalism.L2.G.isUnit_det_gram0 (sp : Spaces R F E) : IsUnit sp.gram0.det := by sorry
