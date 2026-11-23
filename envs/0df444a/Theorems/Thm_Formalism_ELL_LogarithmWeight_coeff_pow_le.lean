-- Prove2me | Theorems.Thm_Formalism_ELL_LogarithmWeight_coeff_pow_le
-- name    : Formalism.ELL.LogarithmWeight.coeff_pow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:21.202688+00:00
-- url     : https://prove2.me/theorems/ec0e325a-6b1a-4299-b870-9846d04edbc7
-- title:
--   Logarithm Weight: coeff pow le
-- statement:
--   The Logarithm Weight construction uses the coeff pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L37-L48

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

theorem Formalism.ELL.LogarithmWeight.coeff_pow_le {f : PowerSeries K} {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hf : ∀ n, ‖coeff n f‖ * c ^ n ≤ A) (m n : ℕ) :
    ‖coeff n (f ^ m)‖ * c ^ n ≤ A ^ m := by sorry
