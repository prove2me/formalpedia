-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_liesOver_ne_bot
-- name    : Formalism.MainNotions.J.liesOver_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:42:48.36384+00:00
-- url     : https://prove2.me/theorems/210fbb29-7d62-4d63-a278-888a1d013f15
-- title:
--   J: lies Over ne bot
-- statement:
--   The J construction uses the lies Over ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L20-L24

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

theorem Formalism.MainNotions.J.liesOver_ne_bot (hp : p.Prime) (I : Ideal (𝓞 K)) (hI : I.LiesOver (span {(p : ℤ)})) : I ≠ ⊥ := by sorry
