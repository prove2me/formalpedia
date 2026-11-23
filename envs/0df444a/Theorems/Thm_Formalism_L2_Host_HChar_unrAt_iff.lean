-- Prove2me | Theorems.Thm_Formalism_L2_Host_HChar_unrAt_iff
-- name    : Formalism.L2.Host.HChar.unrAt_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:41.533323+00:00
-- url     : https://prove2.me/theorems/06fe0f48-4424-4738-a539-c689b56dafc9
-- title:
--   HChar: unr At iff
-- statement:
--   The HChar construction uses the unr At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean#L113-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean#L113-L124

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.Host
variable (L : Type) [Field L] [NumberField L]
variable {L}
open Formalism.L2.Host.HChar
variable (χ : HChar L)

theorem Formalism.L2.Host.HChar.unrAt_iff (v : HeightOneSpectrum (𝓞 L)) : χ.UnrAt v ↔ χ.LevelLe v 0 := by sorry
