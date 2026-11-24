-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_unitary_mulVec
-- name    : Formalism.HermitianLatticeCounting.P.euclNorm_unitary_mulVec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:28:34.290608+00:00
-- url     : https://prove2.me/theorems/342f2ef0-823d-4c39-b3f8-9adddea6c2fb
-- title:
--   P: eucl Norm unitary mul Vec
-- statement:
--   The P construction uses the eucl Norm unitary mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L263-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L263-L269

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

theorem Formalism.HermitianLatticeCounting.P.euclNorm_unitary_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] {k : Matrix ι ι ℂ} (hk : k ∈ Matrix.unitaryGroup ι ℂ)
    (v : ι → ℂ) : n2G (k *ᵥ v) = n2G v := by sorry
