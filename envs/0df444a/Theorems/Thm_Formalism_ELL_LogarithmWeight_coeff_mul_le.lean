-- Prove2me | Theorems.Thm_Formalism_ELL_LogarithmWeight_coeff_mul_le
-- name    : Formalism.ELL.LogarithmWeight.coeff_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:59.61079+00:00
-- url     : https://prove2.me/theorems/6a3d91d0-0c54-4c2c-944c-4ab1cbd17484
-- title:
--   Logarithm Weight: coeff mul le
-- statement:
--   The Logarithm Weight construction uses the coeff mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L25-L35

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

theorem Formalism.ELL.LogarithmWeight.coeff_mul_le {f g : PowerSeries K} {c A B : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ n, ‖coeff n f‖ * c ^ n ≤ A) (hg : ∀ n, ‖coeff n g‖ * c ^ n ≤ B) (n : ℕ) :
    ‖coeff n (f * g)‖ * c ^ n ≤ A * B := by sorry
