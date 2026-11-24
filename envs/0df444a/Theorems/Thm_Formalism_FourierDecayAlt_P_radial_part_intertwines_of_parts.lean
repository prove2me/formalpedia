-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_radial_part_intertwines_of_parts
-- name    : Formalism.FourierDecayAlt.P.radial_part_intertwines_of_parts
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:55.93204+00:00
-- url     : https://prove2.me/theorems/f5bf9dcd-1f0c-4ae5-b644-ee945957c7b9
-- title:
--   P: radial part intertwines of parts
-- statement:
--   The P construction uses the radial part intertwines of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellInversePair.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellInversePair.lean#L76-L79

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
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

theorem Formalism.FourierDecayAlt.P.radial_part_intertwines_of_parts : Formalism.FourierDecayAlt.JF.RadialPartIntertwinesFromComponents := by sorry
