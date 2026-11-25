-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_psiQUnique_true
-- name    : Formalism.FourierDecayAlt.P.psiQUnique_true
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:00.7041+00:00
-- url     : https://prove2.me/theorems/a2865fc5-2b73-5e2f-8228-2bd35abc532a
-- title:
--   P: psi QUnique true
-- statement:
--   The P construction uses the psi QUnique true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellZetaMinors.lean#L53-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellZetaMinors.lean#L53-L67

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

theorem Formalism.FourierDecayAlt.P.psiQUnique_true : Formalism.FourierDecayAlt.JF.PsiQUnique := by sorry
