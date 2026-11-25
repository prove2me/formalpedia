-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Calc_two_torsion_free
-- name    : Formalism.L2.Th1.C.Calc.two_torsion_free
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:35:25.312563+00:00
-- url     : https://prove2.me/theorems/c04bec38-9676-44da-b627-946512c2add7
-- title:
--   Calc: two torsion free
-- statement:
--   The Calc construction uses the two torsion free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/UnitaryInverseIdentity.lean#L401-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/UnitaryInverseIdentity.lean#L401-L406

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ArithmeticFrobeniusAction
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourFoldOrthogonalSum
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FinsuppZmodOneEqSingle
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_GL3MeanSquares_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_UnitaryInverseIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Calc
open Pts Formalism.HermitianLattices.IntegralLatticeDensity
variable {K : Type} [Field K] [CharZero K] {O : Type} [CommRing O] [StarRing O]
variable {R : Subring K} {l linv : PowerSeries K} {τ : O →+* K}

theorem Formalism.L2.Th1.C.Calc.two_torsion_free (D : Data R l linv τ) (h2 : (2 : K)⁻¹ ∈ R) {σ : Type}
    (x : Ser τ σ ⧸ lgSub D σ) (hx : x + x = 0) : x = 0 := by sorry
