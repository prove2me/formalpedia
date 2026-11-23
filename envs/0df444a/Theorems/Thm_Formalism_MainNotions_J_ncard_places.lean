-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_ncard_places
-- name    : Formalism.MainNotions.J.ncard_places
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:42:28.603834+00:00
-- url     : https://prove2.me/theorems/741eedf1-7146-4a78-a1d3-f7026f23cde7
-- title:
--   J: ncard places
-- statement:
--   The J construction uses the ncard places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L47-L52

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

theorem Formalism.MainNotions.J.ncard_places (hp : p.Prime) :
    ({v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}).ncard =
      (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card := by sorry
