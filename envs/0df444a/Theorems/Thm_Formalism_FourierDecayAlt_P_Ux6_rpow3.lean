-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_rpow3
-- name    : Formalism.FourierDecayAlt.P.Ux6.rpow3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:34:50.031146+00:00
-- url     : https://prove2.me/theorems/d1446d89-4f75-4965-b4fa-dc5544cbac51
-- title:
--   Ux6: rpow3
-- statement:
--   The Ux6 construction uses the rpow3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L483-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L483-L485

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6

theorem Formalism.FourierDecayAlt.P.Ux6.rpow3 {A B W a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    (A * B * W) ^ (-a) = (A ^ (-a) * B ^ (-a)) * W ^ (-a) := by sorry
