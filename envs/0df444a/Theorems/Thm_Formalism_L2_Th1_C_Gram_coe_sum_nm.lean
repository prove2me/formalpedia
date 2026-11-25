-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Gram_coe_sum_nm
-- name    : Formalism.L2.Th1.C.Gram.coe_sum_nm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:38:11.821617+00:00
-- url     : https://prove2.me/theorems/3729fe85-24ea-5758-a4e3-23667c441148
-- title:
--   Gram: coe sum nm
-- statement:
--   The Gram construction uses the coe sum nm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/TraceDiagonalBis.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/TraceDiagonalBis.lean#L16-L19

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_GramFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_UnitaryInverseIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CharacterExistsAllEmbeddings
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_TraceDiagonalBis
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
open Formalism.L2.Th1.C.Gram
open Pts Calc Formalism.HermitianLattices.IntegralLatticeDensity

theorem Formalism.L2.Th1.C.Gram.coe_sum_nm {O : Type} [CommRing O] [StarRing O] {n : Type} [Fintype n] (a : n → O) :
    ((∑ i, nm (a i) : saRing O) : O) = ∑ i, star (a i) * a i := by sorry
