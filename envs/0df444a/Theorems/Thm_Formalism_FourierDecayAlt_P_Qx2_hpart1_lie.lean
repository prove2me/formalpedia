-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart1_lie
-- name    : Formalism.FourierDecayAlt.P.Qx2.hpart1_lie
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:10:05.283838+00:00
-- url     : https://prove2.me/theorems/90d61b83-9860-4104-95e2-5c5b7f605a0c
-- title:
--   Qx2: hpart1 lie
-- statement:
--   The Qx2 construction uses the hpart1 lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L103-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L103-L113

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

theorem Formalism.FourierDecayAlt.P.Qx2.hpart1_lie (Z : Mx k r) :
    (hpart1 (Hpk k r) Z)ᴴ * Hpk k r + Hpk k r * hpart1 (Hpk k r) Z = 0 := by sorry
