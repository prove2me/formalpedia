-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellZetaMinors_one_uw
-- name    : Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:03:21.180671+00:00
-- url     : https://prove2.me/theorems/32bc4b70-485b-48e7-a6a2-48aa78bf3c8f
-- title:
--   Big Cell Zeta Minors: one uw
-- statement:
--   The Big Cell Zeta Minors construction uses the one uw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellZetaMinors.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellZetaMinors.lean#L18-L20

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellZetaMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat k r) ∈ UWset k r z := by sorry
