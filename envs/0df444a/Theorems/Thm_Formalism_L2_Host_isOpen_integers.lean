-- Prove2me | Theorems.Thm_Formalism_L2_Host_isOpen_integers
-- name    : Formalism.L2.Host.isOpen_integers
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:33.402863+00:00
-- url     : https://prove2.me/theorems/4d83430d-8f9d-4daa-80f1-1223ed08407d
-- title:
--   Host: is Open integers
-- statement:
--   The Host construction uses the is Open integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAEPf.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAEPf.lean#L38-L39

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

theorem Formalism.L2.Host.isOpen_integers (v : HeightOneSpectrum (𝓞 L)) : IsOpen ((v.adicCompletionIntegers L : Set (v.adicCompletion L))) := by sorry
