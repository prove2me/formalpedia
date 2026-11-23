-- Prove2me | Theorems.Thm_Formalism_ELL_ExponentialCoefficientWeight_inv_le
-- name    : Formalism.ELL.ExponentialCoefficientWeight.inv_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:24.971866+00:00
-- url     : https://prove2.me/theorems/6c4fc180-d907-4c56-b600-55a325437db1
-- title:
--   Exponential Coefficient Weight: inv le
-- statement:
--   The Exponential Coefficient Weight construction uses the inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExpWeight.lean#L63-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExpWeight.lean#L63-L130

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

theorem Formalism.ELL.ExponentialCoefficientWeight.inv_le {l E : PowerSeries K} {r : ℝ} (hr : 0 < r)
    (hE0 : constantCoeff E = 0) (hl1 : coeff 1 l = 1)
    (hl : ∀ m, 2 ≤ m → ‖coeff m l‖ ≤ r⁻¹ * r ^ m)
    (hsub : l.subst E = X) :
    ∀ n, 1 ≤ n → ‖coeff n E‖ ≤ r⁻¹ * r ^ n := by sorry
