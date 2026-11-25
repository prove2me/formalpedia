-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_mem_comap_cj
-- name    : Formalism.FourierDecayAlt.P.Cx2.mem_comap_cj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:49:20.6788+00:00
-- url     : https://prove2.me/theorems/2dec3f31-c8a8-4a7e-a204-56eddda0a683
-- title:
--   Cx2: mem comap cj
-- statement:
--   The Cx2 construction uses the mem comap cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L157-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L157-L181

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

theorem Formalism.FourierDecayAlt.P.Cx2.mem_comap_cj (S : HidaSetting E Wp Wq) (L : Submodule ℤ E) (x : J.CV E) :
    x ∈ ZLattice.comap ℝ (J.eLat E L 1) (cj S).toLinearEquiv.toLinearMap ↔
      ∃ t ∈ L, ∀ v, x (S.pl v) = S.σ v t := by sorry
