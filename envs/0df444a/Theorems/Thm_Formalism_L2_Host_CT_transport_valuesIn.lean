-- Prove2me | Theorems.Thm_Formalism_L2_Host_CT_transport_valuesIn
-- name    : Formalism.L2.Host.CT.transport_valuesIn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:48.947476+00:00
-- url     : https://prove2.me/theorems/eb87b85a-d7f6-4f2a-9544-0a50813789f5
-- title:
--   CT: transport values In
-- statement:
--   The CT construction uses the transport values In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L401-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L401-L413

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

theorem Formalism.L2.Host.CT.transport_valuesIn (j : E ≃+* L) (χ : HChar L) (s : ℝ) {C : Type} [Field C] (e : C →+* ℂ) :
    (transport j χ).ValuesIn s e ↔ χ.ValuesIn s e := by sorry
