-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_hs_mul_unitary
-- name    : Formalism.HermitianLatticeCounting.P.hs_mul_unitary
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:28:24.287842+00:00
-- url     : https://prove2.me/theorems/918a96f3-9890-45a3-b4ad-9fe48c03e62b
-- title:
--   P: hs mul unitary
-- statement:
--   The P construction uses the hs mul unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L51-L55

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

theorem Formalism.HermitianLatticeCounting.P.hs_mul_unitary {N : ℕ} {k : Matrix (Fin N) (Fin N) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin N) ℂ) (Y : Matrix (Fin N) (Fin N) ℂ) : hs (Y * k) = hs Y := by sorry
