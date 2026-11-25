-- Prove2me | Theorems.Thm_Formalism_L2_Host_HChar_val_principal
-- name    : Formalism.L2.Host.HChar.val_principal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:24.782834+00:00
-- url     : https://prove2.me/theorems/63e04445-d4b3-4bba-b071-f168b1e29363
-- title:
--   HChar: val principal
-- statement:
--   The HChar construction uses the val principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharProd.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharProd.lean#L14-L16

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HeckeProd
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.Host Formalism.L2.Host.HChar
variable {L : Type} [Field L] [NumberField L] (χ : HChar L)

theorem Formalism.L2.Host.HChar.val_principal (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : ∀ v, v ∉ S → χ.UnrAt v) (k : Lˣ) :
    (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), χ.val v ^ ordF v k) = (χ.inf k * ∏ v ∈ S, χ.locK v k)⁻¹ := by sorry
