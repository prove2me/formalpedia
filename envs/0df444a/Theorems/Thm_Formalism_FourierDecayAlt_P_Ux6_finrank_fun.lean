-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_finrank_fun
-- name    : Formalism.FourierDecayAlt.P.Ux6.finrank_fun
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:23:09.099504+00:00
-- url     : https://prove2.me/theorems/da0eb2d3-8d73-4c66-bdbb-3ccd67716072
-- title:
--   Ux6: finrank fun
-- statement:
--   The Ux6 construction uses the finrank fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L460-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L460-L461

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

theorem Formalism.FourierDecayAlt.P.Ux6.finrank_fun (ι : Type) [Fintype ι] : Module.finrank ℝ (ι → ℂ) = Fintype.card ι * 2 := by sorry
