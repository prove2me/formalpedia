-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_inv
-- name    : Formalism.FourierDecayAlt.P.Qx2.hpk_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:16.494547+00:00
-- url     : https://prove2.me/theorems/199c4bdc-4567-4068-acc7-85343887f79a
-- title:
--   Qx2: hpk inv
-- statement:
--   The Qx2 construction uses the hpk inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L101-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L101-L101

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.Qx2.hpk_inv : (Hpk k r)⁻¹ = Hpk k r := by sorry
