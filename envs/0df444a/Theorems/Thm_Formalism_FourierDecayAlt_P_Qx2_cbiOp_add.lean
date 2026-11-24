-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_cbiOp_add
-- name    : Formalism.FourierDecayAlt.P.Qx2.cbiOp_add
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:19:52.796182+00:00
-- url     : https://prove2.me/theorems/ea979c06-8a17-400b-85fd-6c8269692465
-- title:
--   Qx2: cbi Op add
-- statement:
--   The Qx2 construction uses the cbi Op add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L33-L35

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}

theorem Formalism.FourierDecayAlt.P.Qx2.cbiOp_add (l : Fin m) (f g : (Fin m → ℂ) → E) : cbiOp l (f + g) = cbiOp l f + cbiOp l g := by sorry
