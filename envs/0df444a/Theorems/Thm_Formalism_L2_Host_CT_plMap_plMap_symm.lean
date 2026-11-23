-- Prove2me | Theorems.Thm_Formalism_L2_Host_CT_plMap_plMap_symm
-- name    : Formalism.L2.Host.CT.plMap_plMap_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:56.607315+00:00
-- url     : https://prove2.me/theorems/0d43873b-fc22-4c2a-bf9c-168a7bc21d5f
-- title:
--   CT: pl Map pl Map symm
-- statement:
--   The CT construction uses the pl Map pl Map symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L36-L38

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

theorem Formalism.L2.Host.CT.plMap_plMap_symm (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) : plMap j (plMap j.symm v) = v := by sorry
