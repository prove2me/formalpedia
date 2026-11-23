-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_thetaDomination_dp_of_krPSD_of_domMin
-- name    : Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.thetaDomination_dp_of_krPSD_of_domMin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:33.349786+00:00
-- url     : https://prove2.me/theorems/a785bd1b-43f0-4d1b-aad2-415945dbcbdc
-- title:
--   B1: theta Domination dp of kr PSD of dom Min
-- statement:
--   The B1 construction uses the theta Domination dp of kr PSD of dom Min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L712-L775
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L712-L775

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.thetaDomination_dp_of_krPSD_of_domMin (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) (hK : KrPSD D)
    (hE : EBounds D) (hD : DomMin D T Th) : (Dp D T Th).ThetaDomination := by sorry
