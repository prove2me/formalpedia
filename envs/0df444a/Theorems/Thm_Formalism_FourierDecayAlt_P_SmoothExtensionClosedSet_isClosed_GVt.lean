-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothExtensionClosedSet_isClosed_GVt
-- name    : Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet.isClosed_GVt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:54:03.094917+00:00
-- url     : https://prove2.me/theorems/9dfafef2-c603-4f27-a9ad-1ae215f97c28
-- title:
--   Smooth Extension Closed Set: is Closed GVt
-- statement:
--   The Smooth Extension Closed Set construction uses the is Closed GVt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsSmoothExt.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsSmoothExt.lean#L13-L18

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsSmoothExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter Topology
open scoped Manifold ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet.isClosed_GVt (k r : ℕ) : IsClosed {x : Mt k r | Matrix.of x ∈ B.GV k r} := by sorry
