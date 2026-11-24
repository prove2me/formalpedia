-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_map_pI_ne_bot
-- name    : Formalism.MainNotions.J.map_pI_ne_bot
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:57:18.769721+00:00
-- url     : https://prove2.me/theorems/911515cc-7db8-4f45-b5e4-e8cec17d07bd
-- title:
--   J: map p I ne bot
-- statement:
--   The J construction uses the map p I ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L54-L56

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
variable (K : Type) [Field K] [NumberField K] (p : ℕ)

theorem Formalism.MainNotions.J.map_pI_ne_bot (hp : p.Prime) : map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≠ ⊥ := by sorry
