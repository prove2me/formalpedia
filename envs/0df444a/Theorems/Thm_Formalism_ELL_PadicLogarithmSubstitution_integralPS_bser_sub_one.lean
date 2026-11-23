-- Prove2me | Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_integralPS_bser_sub_one
-- name    : Formalism.ELL.PadicLogarithmSubstitution.integralPS_bser_sub_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:41.062297+00:00
-- url     : https://prove2.me/theorems/98f666df-1ba7-4cde-85ab-f39e3bd92328
-- title:
--   Padic Logarithm Substitution: integral PS bser sub one
-- statement:
--   The Padic Logarithm Substitution construction uses the integral PS bser sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L137-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L137-L143

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
variable (p : ℕ) [Fact p.Prime] (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]

theorem Formalism.ELL.PadicLogarithmSubstitution.integralPS_bser_sub_one [IsUltrametricDist K] (b : ℤ_[p]) :
    IntegralPS (bser p K b - 1) := by sorry
