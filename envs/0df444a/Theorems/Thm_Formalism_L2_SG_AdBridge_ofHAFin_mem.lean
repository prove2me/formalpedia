-- Prove2me | Theorems.Thm_Formalism_L2_SG_AdBridge_ofHAFin_mem
-- name    : Formalism.L2.SG.AdBridge.ofHAFin_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:40:19.78371+00:00
-- url     : https://prove2.me/theorems/92aafa76-5b3b-4d67-9e6a-a5ab54329c51
-- title:
--   Ad Bridge: of HAFin mem
-- statement:
--   The Ad Bridge construction uses the of HAFin mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FundamentalEquivalence/AdBridge.lean#L248-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FundamentalEquivalence/AdBridge.lean#L248-L269

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AdBridge
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
variable (I : AutInst)

theorem Formalism.L2.SG.AdBridge.ofHAFin_mem (h : HAd I) :
    Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (ofHAFin I h) *
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * ofHAFin I h =
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by sorry
