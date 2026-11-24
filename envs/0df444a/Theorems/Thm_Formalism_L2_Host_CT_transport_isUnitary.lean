-- Prove2me | Theorems.Thm_Formalism_L2_Host_CT_transport_isUnitary
-- name    : Formalism.L2.Host.CT.transport_isUnitary
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:23:24.941396+00:00
-- url     : https://prove2.me/theorems/284a69c4-aad3-4a5b-ad8d-847f2451014c
-- title:
--   CT: transport is Unitary
-- statement:
--   The CT construction uses the transport is Unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L397-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L397-L399

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

theorem Formalism.L2.Host.CT.transport_isUnitary (j : E ≃+* L) (χ : HChar L) (h : χ.IsUnitary) : (transport j χ).IsUnitary := by sorry
