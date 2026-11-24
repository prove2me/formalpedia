-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_lam
-- name    : Formalism.FourierDecayAlt.Q.QRR.lam
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:42:36.13063+00:00
-- url     : https://prove2.me/theorems/0bf6cea5-8f1d-4db1-9af8-4fa081caf284
-- title:
--   QRR: lam
-- statement:
--   The QRR construction uses the lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/PatEntryZero.lean#L339-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/PatEntryZero.lean#L339-L371

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.QRR.lam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (l : Fin r) (D : Set (Mx k r)) (f : Mx k r → E) (hR : RightEq k r z l.castSucc D f)
    (g : Mx k r) (hg : g ∈ Glev k r l.castSucc ∩ D) (Z : Mx k r) (hZ : Pat k r l Z) :
    RdV (hpart1 (Hpk k r) Z) f g + Complex.I • RdV (hpart2 (Hpk k r) Z) f g =
      (ell k r z Z + star (ell k r z (dag k r Z))) • f g := by sorry
