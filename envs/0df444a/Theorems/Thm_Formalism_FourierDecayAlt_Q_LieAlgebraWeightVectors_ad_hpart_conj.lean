-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_hpart_conj
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_hpart_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:44:38.009211+00:00
-- url     : https://prove2.me/theorems/ea2b3a4a-df4e-4794-89f4-f212c42c11fc
-- title:
--   Lie Algebra Weight Vectors: ad hpart conj
-- statement:
--   The Lie Algebra Weight Vectors construction uses the ad hpart conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBCtMulVec.lean#L107-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBCtMulVec.lean#L107-L132

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_hpart_conj {g : Mx k r} (hg : gᴴ * Hpk k r * g = Hpk k r) (hgi : g * g⁻¹ = 1) (Z : Mx k r) :
    hpart1 (Hpk k r) (g * Z * g⁻¹) = g * hpart1 (Hpk k r) Z * g⁻¹ ∧
      hpart2 (Hpk k r) (g * Z * g⁻¹) = g * hpart2 (Hpk k r) Z * g⁻¹ := by sorry
