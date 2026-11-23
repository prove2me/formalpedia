-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_thetaDomination_d_of_axK_of_domMinA
-- name    : Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.thetaDomination_d_of_axK_of_domMinA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:33.460458+00:00
-- url     : https://prove2.me/theorems/f48bf989-d1f1-447c-9ebc-655aaf959a9e
-- title:
--   A1: theta Domination d of ax K of dom Min A
-- statement:
--   The A1 construction uses the theta Domination d of ax K of dom Min A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L331-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L331-L377

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]

theorem Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.thetaDomination_d_of_axK_of_domMinA (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hNZ : NZSg Sg) (hK : AxK D)
    (hD : TC.DomMinA D Sg Th) : ThetaDomination (D' D Sg Th) := by sorry
