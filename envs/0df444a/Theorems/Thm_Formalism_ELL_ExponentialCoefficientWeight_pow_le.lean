-- Prove2me | Theorems.Thm_Formalism_ELL_ExponentialCoefficientWeight_pow_le
-- name    : Formalism.ELL.ExponentialCoefficientWeight.pow_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:13.644123+00:00
-- url     : https://prove2.me/theorems/b9674ce3-ccb3-4189-b62f-f4150b7d2f00
-- title:
--   Exponential Coefficient Weight: pow le
-- statement:
--   The Exponential Coefficient Weight construction uses the pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExpWeight.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExpWeight.lean#L28-L42

import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExpWeight
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
open Formalism Formalism.ELL Formalism.ELL.ExponentialCoefficientWeight
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.ExponentialCoefficientWeight.pow_le {f : PowerSeries K} {r A : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A) {N : ℕ}
    (hf : ∀ d ≤ N, ‖coeff d f‖ ≤ A * r ^ d) :
    ∀ m : ℕ, ∀ d ≤ N, ‖coeff d (f ^ m)‖ ≤ A ^ m * r ^ d := by sorry
