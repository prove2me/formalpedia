-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_ef_one_sub
-- name    : Formalism.MainNotions.J.ef_one_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:57:08.225924+00:00
-- url     : https://prove2.me/theorems/0b2adadd-290b-454f-be16-db8503babc35
-- title:
--   J: ef one sub
-- statement:
--   The J construction uses the ef one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L93-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L93-L127

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
variable (L : Type) [Field L] [NumberField L] [Algebra K L]

theorem Formalism.MainNotions.J.ef_one_sub (hp : p.Prime)
    (hL : ∀ Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 L),
      (span {(p : ℤ)}).ramificationIdx' Q * (span {(p : ℤ)}).inertiaDeg' Q = 1) :
    ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1 := by sorry
