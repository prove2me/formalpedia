-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelGenB_val_int
-- name    : Formalism.MainNotions.BridgeLevelGenB.val_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:40:21.859798+00:00
-- url     : https://prove2.me/theorems/36cb7266-66e3-4168-bc8d-5d05954794e6
-- title:
--   Bridge Level Gen B: val int
-- statement:
--   The Bridge Level Gen B construction uses the val int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGenB.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGenB.lean#L13-L15

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]

theorem Formalism.MainNotions.BridgeLevelGenB.val_int (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) = v.intValuation a := by sorry
