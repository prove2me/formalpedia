-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_covolume_comap_cj
-- name    : Formalism.FourierDecayAlt.P.Cx2.covolume_comap_cj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:27:40.674555+00:00
-- url     : https://prove2.me/theorems/7b26f4a4-e0a6-5157-8674-4d973acc8778
-- title:
--   Cx2: covolume comap cj
-- statement:
--   The Cx2 construction uses the covolume comap cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L183-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L183-L187

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
variable {Wp Wq : InfinitePlace E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem Formalism.FourierDecayAlt.P.Cx2.covolume_comap_cj (S : HidaSetting E Wp Wq) (L : Submodule ℤ E) [DiscreteTopology (J.eLat E L 1)]
    [IsZLattice ℝ (J.eLat E L 1)] :
    ZLattice.covolume (ZLattice.comap ℝ (J.eLat E L 1) (cj S).toLinearEquiv.toLinearMap) =
      ZLattice.covolume (J.eLat E L 1) := by sorry
