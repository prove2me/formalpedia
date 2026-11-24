-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_opnorm_unitary_exp_le
-- name    : Formalism.HermitianLatticeCounting.P.opnorm_unitary_exp_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:28:34.469967+00:00
-- url     : https://prove2.me/theorems/9389bfdf-c521-4652-8d5a-e5b3ad28db31
-- title:
--   P: opnorm unitary exp le
-- statement:
--   The P construction uses the opnorm unitary exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L271-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L271-L292

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

theorem Formalism.HermitianLatticeCounting.P.opnorm_unitary_exp_le {ι : Type} [Fintype ι] [DecidableEq ι] {k : Matrix ι ι ℂ}
    (hk : k ∈ Matrix.unitaryGroup ι ℂ) (Y : Matrix ι ι ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (k * NormedSpace.exp Y))‖
      ≤ Real.exp (hsG Y) := by sorry
