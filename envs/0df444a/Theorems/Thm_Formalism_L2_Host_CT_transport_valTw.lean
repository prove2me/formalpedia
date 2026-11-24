-- Prove2me | Theorems.Thm_Formalism_L2_Host_CT_transport_valTw
-- name    : Formalism.L2.Host.CT.transport_valTw
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:43.205821+00:00
-- url     : https://prove2.me/theorems/aabc2c57-6c6c-4c00-b36b-97e12586aee7
-- title:
--   CT: transport val Tw
-- statement:
--   The CT construction uses the transport val Tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L392-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L392-L395

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

theorem Formalism.L2.Host.CT.transport_valTw (j : E ≃+* L) (χ : HChar L) (s : ℝ) (w : HeightOneSpectrum (𝓞 E)) (h : χ.UnrAt (plMap j w)) :
    (transport j χ).valTw s w = χ.valTw s (plMap j w) := by sorry
