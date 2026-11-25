-- Prove2me | Theorems.Thm_Formalism_L2_Host_CT_finMap_apply
-- name    : Formalism.L2.Host.CT.finMap_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:39.97939+00:00
-- url     : https://prove2.me/theorems/1b5bf34b-1c5f-4dc3-8344-4fb01247a274
-- title:
--   CT: fin Map apply
-- statement:
--   The CT construction uses the fin Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L264-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L264-L265

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host Formalism.L2.Host.CT
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]

theorem Formalism.L2.Host.CT.finMap_apply (j : E ≃+* L) (a : FiniteAdeleRing (𝓞 E) E) (v : HeightOneSpectrum (𝓞 L)) :
    finMap j a v = (compEquiv j.symm v).symm (a (plMap j.symm v)) := by sorry
