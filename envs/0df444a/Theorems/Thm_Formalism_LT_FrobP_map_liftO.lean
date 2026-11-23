-- Prove2me | Theorems.Thm_Formalism_LT_FrobP_map_liftO
-- name    : Formalism.LT.FrobP.map_liftO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:41.07809+00:00
-- url     : https://prove2.me/theorems/92b95659-8702-4da7-954d-df1d2f80f599
-- title:
--   Frob P: map lift O
-- statement:
--   The Frob P construction uses the map lift O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MemSpanOfNormLe.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MemSpanOfNormLe.lean#L79-L83

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.LT Formalism.LT.FrobP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.FrobP.map_liftO {ι : Type v} (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    MvPowerSeries.map (unitBall K).subtype (liftO A hA) = A := by sorry
