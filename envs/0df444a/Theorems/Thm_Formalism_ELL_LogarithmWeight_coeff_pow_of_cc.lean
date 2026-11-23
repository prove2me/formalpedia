-- Prove2me | Theorems.Thm_Formalism_ELL_LogarithmWeight_coeff_pow_of_cc
-- name    : Formalism.ELL.LogarithmWeight.coeff_pow_of_cc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:43.72482+00:00
-- url     : https://prove2.me/theorems/115e11da-1879-4de9-a3aa-32cdd565bdec
-- title:
--   Logarithm Weight: coeff pow of cc
-- statement:
--   The Logarithm Weight construction uses the coeff pow of cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L50-L57

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

theorem Formalism.ELL.LogarithmWeight.coeff_pow_of_cc {e : PowerSeries K} (he : constantCoeff e = 0) :
    ∃ g : PowerSeries K, constantCoeff g = coeff 1 e ∧
      ∀ m n : ℕ, coeff n (e ^ m) = if m ≤ n then coeff (n - m) (g ^ m) else 0 := by sorry
