-- Prove2me | Theorems.Thm_Formalism_L2_Host_unif_spec
-- name    : Formalism.L2.Host.unif_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:26.340107+00:00
-- url     : https://prove2.me/theorems/a79782e2-d17a-4810-8e5d-fca9e25f8792
-- title:
--   Host: unif spec
-- statement:
--   The Host construction uses the unif spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean#L52-L53

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

theorem Formalism.L2.Host.unif_spec (v : HeightOneSpectrum (𝓞 L)) : IsUnifAt v (atFin v (unif v)) := by sorry
