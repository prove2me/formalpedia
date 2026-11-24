-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_kap_mem
-- name    : Formalism.FourierDecayAlt.P.Ux1.kap_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:10:37.647198+00:00
-- url     : https://prove2.me/theorems/d0b08141-5216-4c36-aa75-c233215aa5ad
-- title:
--   Ux1: kap mem
-- statement:
--   The Ux1 construction uses the kap mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L191-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L191-L192

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_UpperTheory_Reformulated_B_Qj14_kap_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux1.kap_mem {Y : Mat k r} (hY : inLie k r Y) (hu : IsUnit (1 - Y).det) : kap Y ∈ GV k r := by sorry
