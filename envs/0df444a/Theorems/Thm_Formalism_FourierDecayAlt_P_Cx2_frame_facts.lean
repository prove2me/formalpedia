-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_frame_facts
-- name    : Formalism.FourierDecayAlt.P.Cx2.frame_facts
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:15:47.83085+00:00
-- url     : https://prove2.me/theorems/eb0910c7-7e94-49f6-98bc-1b344cd5cedf
-- title:
--   Cx2: frame facts
-- statement:
--   The Cx2 construction uses the frame facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L49-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L49-L82

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

theorem Formalism.FourierDecayAlt.P.Cx2.frame_facts (g : ℕ) (hg : 0 < g) (ν : ℤ) :
    DiscreteTopology (S6.frameLat E (S6.perLat E g ν 1) 1) ∧
    Submodule.span ℝ (S6.frameLat E (S6.perLat E g ν 1) 1 : Set (mixedEmbedding.mixedSpace E)) = ⊤ := by sorry
