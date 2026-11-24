-- Prove2me | Theorems.Thm_Formalism_L2_Host_mem_integers_of_isUnitAt
-- name    : Formalism.L2.Host.mem_integers_of_isUnitAt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:33.873497+00:00
-- url     : https://prove2.me/theorems/70a277f3-0ad0-47ca-bc6f-53b2bce94f16
-- title:
--   Host: mem integers of is Unit At
-- statement:
--   The Host construction uses the mem integers of is Unit At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAEPf.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAEPf.lean#L80-L83

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

theorem Formalism.L2.Host.mem_integers_of_isUnitAt {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) :
    (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by sorry
