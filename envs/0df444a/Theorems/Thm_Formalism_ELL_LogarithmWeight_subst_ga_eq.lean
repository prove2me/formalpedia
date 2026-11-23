-- Prove2me | Theorems.Thm_Formalism_ELL_LogarithmWeight_subst_ga_eq
-- name    : Formalism.ELL.LogarithmWeight.subst_ga_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:47.312008+00:00
-- url     : https://prove2.me/theorems/09fe7d04-355a-4842-804b-bde34d62b762
-- title:
--   Logarithm Weight: subst ga eq
-- statement:
--   The Logarithm Weight construction uses the subst ga eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L81-L88

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.LogarithmWeight
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.LogarithmWeight.subst_ga_eq {R : Type*} [CommRing R] (f : PowerSeries R) (hf0 : constantCoeff f = 0) :
    (FormalGroup.𝔾ₐ (R := R)).toPowerSeries.subst ![atX f, atY f] = atX f + atY f := by sorry
