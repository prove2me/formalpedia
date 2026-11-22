-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_pI_max
-- name    : Formalism.MainNotions.J.pI_max
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:52.164797+00:00
-- url     : https://prove2.me/theorems/4979b581-bb8e-41da-a1ec-cad599a67411
-- title:
--   J: p I max
-- statement:
--   The J construction uses the p I max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L17-L18

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

theorem Formalism.MainNotions.J.pI_max (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ).IsMaximal := by sorry
