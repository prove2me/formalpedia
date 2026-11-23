-- Prove2me | Theorems.Thm_Formalism_ELL_ExponentialCoefficientWeight_mul_le
-- name    : Formalism.ELL.ExponentialCoefficientWeight.mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:16.609429+00:00
-- url     : https://prove2.me/theorems/0639e832-42c1-494b-a55d-ba2c6abe5149
-- title:
--   Exponential Coefficient Weight: mul le
-- statement:
--   The Exponential Coefficient Weight construction uses the mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExpWeight.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExpWeight.lean#L13-L26

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

theorem Formalism.ELL.ExponentialCoefficientWeight.mul_le {f g : PowerSeries K} {r A B : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {N : ℕ} (hf : ∀ d ≤ N, ‖coeff d f‖ ≤ A * r ^ d) (hg : ∀ d ≤ N, ‖coeff d g‖ ≤ B * r ^ d) :
    ∀ d ≤ N, ‖coeff d (f * g)‖ ≤ (A * B) * r ^ d := by sorry
