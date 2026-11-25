-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_coordinate_sizes_of_hypotheses
-- name    : Formalism.FourierDecayAlt.P.Ux6.coordinate_sizes_of_hypotheses
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:28:57.896475+00:00
-- url     : https://prove2.me/theorems/7513aada-9034-45c8-97b3-3da4b5db94be
-- title:
--   Ux6: coordinate sizes of hypotheses
-- statement:
--   The Ux6 construction uses the coordinate sizes of hypotheses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L544-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L544-L545

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

theorem Formalism.FourierDecayAlt.P.Ux6.coordinate_sizes_of_hypotheses (hSM : SliceMem) (hU1 : BigCellCoordinateSizes) (hU2 : BlockHeadSizes) (hZh : ZhSlice) : SliceCoordinateSizes := by sorry
