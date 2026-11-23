-- Prove2me | Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_integralMv_subst
-- name    : Formalism.ELL.PadicLogarithmSubstitution.integralMv_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:34.075837+00:00
-- url     : https://prove2.me/theorems/5411f856-d566-4943-95c2-5b027167a2d4
-- title:
--   Padic Logarithm Substitution: integral Mv subst
-- statement:
--   The Padic Logarithm Substitution construction uses the integral Mv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L42-L49

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
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.PadicLogarithmSubstitution.integralMv_subst {σ : Type*} {a : PowerSeries K} (ha : IntegralPS a)
    {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0) (hf : IntegralMv f) :
    IntegralMv (a.subst f) := by sorry
