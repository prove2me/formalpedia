-- Prove2me | Theorems.Thm_Formalism_L2_Host_HChar_val_eq
-- name    : Formalism.L2.Host.HChar.val_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:01.54634+00:00
-- url     : https://prove2.me/theorems/fe6d9e08-618f-4d3b-a895-33a8dbac3d33
-- title:
--   HChar: val eq
-- statement:
--   The HChar construction uses the val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean#L126-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean#L126-L138

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

theorem Formalism.L2.Host.HChar.val_eq {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) (x : (v.adicCompletion L)ˣ) (hx : IsUnifAt v x) :
    χ.loc v x = χ.val v := by sorry
