-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_unitary_conj
-- name    : Formalism.HermitianLatticeCounting.P.unitary_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:28:18.978856+00:00
-- url     : https://prove2.me/theorems/02ed2807-9fbf-4920-ade1-1eef82c1ec08
-- title:
--   P: unitary conj
-- statement:
--   The P construction uses the unitary conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean#L78-L81

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

theorem Formalism.HermitianLatticeCounting.P.unitary_conj {N : ℕ} {k : Matrix (Fin N) (Fin N) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    kᴴ ∈ Matrix.unitaryGroup (Fin N) ℂ := by sorry
