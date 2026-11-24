-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_hpart_kill
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_hpart_kill
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:45:29.500455+00:00
-- url     : https://prove2.me/theorems/a07d06da-53f9-4b93-a9e2-9a23b3bcfa38
-- title:
--   Lie Algebra Weight Vectors: ad hpart kill
-- statement:
--   The Lie Algebra Weight Vectors construction uses the ad hpart kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBCtMulVec.lean#L67-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBCtMulVec.lean#L67-L79

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_hpart_kill {Z : Mx k r} {v : Fin (2 * r + k + 1) → ℂ} (h1 : Z *ᵥ v = 0)
    (h2 : Zᴴ *ᵥ (Hpk k r *ᵥ v) = 0) :
    hpart1 (Hpk k r) Z *ᵥ v = 0 ∧ hpart2 (Hpk k r) Z *ᵥ v = 0 := by sorry
