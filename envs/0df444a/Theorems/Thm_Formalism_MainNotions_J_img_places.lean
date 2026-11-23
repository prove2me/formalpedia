-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_img_places
-- name    : Formalism.MainNotions.J.img_places
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:42:39.775059+00:00
-- url     : https://prove2.me/theorems/33a87a4d-a8b4-46b1-99bb-39d4eca647c1
-- title:
--   J: img places
-- statement:
--   The J construction uses the img places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L26-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L26-L45

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

theorem Formalism.MainNotions.J.img_places (hp : p.Prime) :
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} =
      (span {(p : ℤ)}).primesOver (𝓞 K) := by sorry
