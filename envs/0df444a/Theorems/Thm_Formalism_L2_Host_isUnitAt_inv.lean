-- Prove2me | Theorems.Thm_Formalism_L2_Host_isUnitAt_inv
-- name    : Formalism.L2.Host.isUnitAt_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:41.047341+00:00
-- url     : https://prove2.me/theorems/da2c2c14-5cf8-4cce-bd56-890ca8cf30a8
-- title:
--   Host: is Unit At inv
-- statement:
--   The Host construction uses the is Unit At inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAEPf.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAEPf.lean#L85-L87

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAEPf
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
open Formalism Formalism.L2 Formalism.L2.Host
variable {L : Type} [Field L] [NumberField L]

theorem Formalism.L2.Host.isUnitAt_inv {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) : IsUnitAt v x⁻¹ := by sorry
