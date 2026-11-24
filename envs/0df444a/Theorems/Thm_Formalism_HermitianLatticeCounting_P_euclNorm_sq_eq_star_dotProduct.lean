-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_sq_eq_star_dotProduct
-- name    : Formalism.HermitianLatticeCounting.P.euclNorm_sq_eq_star_dotProduct
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:28:18.795992+00:00
-- url     : https://prove2.me/theorems/03b4b835-b93a-45bb-a4fd-7cbbe3874ce7
-- title:
--   P: eucl Norm sq eq star dot Product
-- statement:
--   The P construction uses the eucl Norm sq eq star dot Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L245-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L245-L249

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.euclNorm_sq_eq_star_dotProduct {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) : ((n2G v ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v := by sorry
