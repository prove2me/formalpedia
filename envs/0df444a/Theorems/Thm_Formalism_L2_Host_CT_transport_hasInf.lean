-- Prove2me | Theorems.Thm_Formalism_L2_Host_CT_transport_hasInf
-- name    : Formalism.L2.Host.CT.transport_hasInf
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:16.357925+00:00
-- url     : https://prove2.me/theorems/83cc2a7f-bf36-4ad5-b72f-49081d38238a
-- title:
--   CT: transport has Inf
-- statement:
--   The CT construction uses the transport has Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L481-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L481-L494

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

theorem Formalism.L2.Host.CT.transport_hasInf (j : E ≃+* L) (χ : HChar L) {I : Type} [Fintype I] (φ : I → E →+* ℂ) (n : I → ℤ) :
    (transport j χ).HasInf φ n ↔ χ.HasInf (fun i => (φ i).comp j.symm.toRingHom) n := by sorry
