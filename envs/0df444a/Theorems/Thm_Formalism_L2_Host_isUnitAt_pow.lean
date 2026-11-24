-- Prove2me | Theorems.Thm_Formalism_L2_Host_isUnitAt_pow
-- name    : Formalism.L2.Host.isUnitAt_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:27.920712+00:00
-- url     : https://prove2.me/theorems/149ce334-ed65-4963-8d93-3a7cbb96c839
-- title:
--   Host: is Unit At pow
-- statement:
--   The Host construction uses the is Unit At pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAEPf.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAEPf.lean#L89-L92

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

theorem Formalism.L2.Host.isUnitAt_pow {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) (n : ℕ) :
    IsUnitAt v (x ^ n) := by sorry
