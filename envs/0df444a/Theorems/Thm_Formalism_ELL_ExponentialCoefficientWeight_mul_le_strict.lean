-- Prove2me | Theorems.Thm_Formalism_ELL_ExponentialCoefficientWeight_mul_le_strict
-- name    : Formalism.ELL.ExponentialCoefficientWeight.mul_le_strict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:10.686277+00:00
-- url     : https://prove2.me/theorems/9dc6ee78-c2b0-45d9-89ad-6e7372fbeabe
-- title:
--   Exponential Coefficient Weight: mul le strict
-- statement:
--   The Exponential Coefficient Weight construction uses the mul le strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExpWeight.lean#L44-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExpWeight.lean#L44-L61

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

theorem Formalism.ELL.ExponentialCoefficientWeight.mul_le_strict {f g : PowerSeries K} {r A B : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hB : 0 ≤ B) {n : ℕ} (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hf : ∀ d < n, ‖coeff d f‖ ≤ A * r ^ d) (hg : ∀ d < n, ‖coeff d g‖ ≤ B * r ^ d) :
    ‖coeff n (f * g)‖ ≤ (A * B) * r ^ n := by sorry
