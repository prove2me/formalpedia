-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_pI_ne_bot
-- name    : Formalism.MainNotions.J.pI_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:57.985401+00:00
-- url     : https://prove2.me/theorems/5b2c88f5-3e23-46bf-9981-a9a9aebd833b
-- title:
--   J: p I ne bot
-- statement:
--   The J construction uses the p I ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L13-L15

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

theorem Formalism.MainNotions.J.pI_ne_bot (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by sorry
