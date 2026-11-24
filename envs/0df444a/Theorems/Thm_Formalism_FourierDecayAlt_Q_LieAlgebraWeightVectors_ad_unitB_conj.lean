-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_unitB_conj
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_unitB_conj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:44:32.2844+00:00
-- url     : https://prove2.me/theorems/d8580402-2bbf-4dd2-9094-2e147759e1ef
-- title:
--   Lie Algebra Weight Vectors: ad unit B conj
-- statement:
--   The Lie Algebra Weight Vectors construction uses the ad unit B conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBCtMulVec.lean#L93-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBCtMulVec.lean#L93-L105

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_unitB_conj {g : Mx k r} (hg : gᴴ * Hpk k r * g = Hpk k r) (hgi : g * g⁻¹ = 1)
    {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m) :
    unitB (Hpk k r) (fun c => g *ᵥ Bs c) a b = g * unitB (Hpk k r) Bs a b * g⁻¹ := by sorry
