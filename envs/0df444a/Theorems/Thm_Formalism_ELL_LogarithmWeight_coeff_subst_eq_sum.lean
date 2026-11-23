-- Prove2me | Theorems.Thm_Formalism_ELL_LogarithmWeight_coeff_subst_eq_sum
-- name    : Formalism.ELL.LogarithmWeight.coeff_subst_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:49.44482+00:00
-- url     : https://prove2.me/theorems/407bb8a5-d3bf-4554-9f96-1b56892aa8b5
-- title:
--   Logarithm Weight: coeff subst eq sum
-- statement:
--   The Logarithm Weight construction uses the coeff subst eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L69-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L69-L79

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

theorem Formalism.ELL.LogarithmWeight.coeff_subst_eq_sum {l e : PowerSeries K} (he : constantCoeff e = 0) (n : ℕ) :
    coeff n (l.subst e) = ∑ m ∈ Finset.range (n + 1), coeff m l * coeff n (e ^ m) := by sorry
