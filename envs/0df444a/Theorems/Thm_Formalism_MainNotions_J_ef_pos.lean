-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_ef_pos
-- name    : Formalism.MainNotions.J.ef_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:16.518134+00:00
-- url     : https://prove2.me/theorems/9b63ea86-2c9c-4d2b-a67d-cda327c3f18d
-- title:
--   J: ef pos
-- statement:
--   The J construction uses the ef pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L58-L66

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

theorem Formalism.MainNotions.J.ef_pos (hp : p.Prime) (P : Ideal (𝓞 K)) (hP : P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)) :
    1 ≤ (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P := by sorry
