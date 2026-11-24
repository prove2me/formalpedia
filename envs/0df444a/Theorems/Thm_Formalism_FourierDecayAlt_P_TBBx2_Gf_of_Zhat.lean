-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Gf_of_Zhat
-- name    : Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:53:20.395938+00:00
-- url     : https://prove2.me/theorems/e7f4bff6-78dd-4a08-9e03-210e622a4a8f
-- title:
--   TBBx2: Gf of Zhat
-- statement:
--   The TBBx2 construction uses the Gf of Zhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L94-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L94-L106

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section

theorem Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (pt : C.LPt)
    (h : Zhat k r z z' g = D.ptMatN pt (r + 1)) :
    Gf k r z z' g = D.ptG (Tz k r z * Tz k r z') r pt := by sorry
