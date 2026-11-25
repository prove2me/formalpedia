-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_skip_one_eq_succAbove
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorCommutation.skip_one_eq_succAbove
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:10:02.454202+00:00
-- url     : https://prove2.me/theorems/cb490898-c266-42c5-9d16-28021e5aa5ad
-- title:
--   Quantum Minor Commutation: skip one eq succ Above
-- statement:
--   The Quantum Minor Commutation construction uses the skip one eq succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L141-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L141-L142

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Theorems.Thm_PI_QnCovHatW_skip_one_eq_succAbove
import Theorems.Thm_PI_QnZeroLevelWork_skip_one_eq_succAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorCommutation
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem Formalism.FourierDecayAlt.P.QuantumMinorCommutation.skip_one_eq_succAbove {m : ℕ} (q : Fin (m + 1)) : (skip1 q : Fin m → Fin (m + 1)) = q.succAbove := by sorry
