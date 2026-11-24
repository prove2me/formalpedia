-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_herm_sum
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_herm_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:44:22.821803+00:00
-- url     : https://prove2.me/theorems/3a42ac19-7122-4be5-8321-3d877952f9b7
-- title:
--   Lie Algebra Weight Vectors: ad herm sum
-- statement:
--   The Lie Algebra Weight Vectors construction uses the ad herm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBCtMulVec.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBCtMulVec.lean#L22-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_herm_sum (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ q, v q * herm (Hpk k r) (bvec q) w := by sorry
