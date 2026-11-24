-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_eq_euclideanSpace_norm
-- name    : Formalism.HermitianLatticeCounting.P.euclNorm_eq_euclideanSpace_norm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:29:30.714842+00:00
-- url     : https://prove2.me/theorems/355de7b3-d053-407f-8d6a-505f159c4867
-- title:
--   P: eucl Norm eq euclidean Space norm
-- statement:
--   The P construction uses the eucl Norm eq euclidean Space norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L238-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L238-L240

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

theorem Formalism.HermitianLatticeCounting.P.euclNorm_eq_euclideanSpace_norm {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    n2G v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ := by sorry
