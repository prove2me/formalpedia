-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_sign_succ
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorExpansion.sign_succ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:10:08.838686+00:00
-- url     : https://prove2.me/theorems/8fa1bd29-a548-444e-ad21-45796a7e4336
-- title:
--   Quantum Minor Expansion: sign succ
-- statement:
--   The Quantum Minor Expansion construction uses the sign succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L144-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L144-L152

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorExpansion
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.Qx6

theorem Formalism.FourierDecayAlt.P.QuantumMinorExpansion.sign_succ {m : ℕ} (q : Fin (m + 1)) (x : Fin m) :
    ((-1 : ℤ) ^ (x : ℕ)) = (-1) ^ ((q.succAbove x : Fin (m + 1)) : ℕ) * eps (q.succAbove x) q := by sorry
