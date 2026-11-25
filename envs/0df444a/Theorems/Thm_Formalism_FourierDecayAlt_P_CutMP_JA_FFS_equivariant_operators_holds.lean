-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_equivariant_operators_holds
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.equivariant_operators_holds
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:29:30.207216+00:00
-- url     : https://prove2.me/theorems/aeccaaf7-7ffd-42ca-82af-c295a47de1a9
-- title:
--   FFS: equivariant operators holds
-- statement:
--   The FFS construction uses the equivariant operators holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableEquivOps.lean#L40-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableEquivOps.lean#L40-L187

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableEquivOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.FFS
open Formalism.QuantumDeterminants.WeylGroupFacts
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutMP.JA.FFS.equivariant_operators_holds : EquivOps := by sorry
