-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_eLat_facts
-- name    : Formalism.FourierDecayAlt.P.Cx2.eLat_facts
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:15:51.610798+00:00
-- url     : https://prove2.me/theorems/02d4f339-c0c6-4004-a622-3d1bca505644
-- title:
--   Cx2: e Lat facts
-- statement:
--   The Cx2 construction uses the e Lat facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L84-L88

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
open Formalism.FourierDecayAlt.P.Cx2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem Formalism.FourierDecayAlt.P.Cx2.eLat_facts (hEF : J.EuclidFrame) (g : ℕ) (hg : 0 < g) (ν : ℤ) :
    ∃ _ : DiscreteTopology (J.eLat E (S6.perLat E g ν 1) 1), IsZLattice ℝ (J.eLat E (S6.perLat E g ν 1) 1) := by sorry
