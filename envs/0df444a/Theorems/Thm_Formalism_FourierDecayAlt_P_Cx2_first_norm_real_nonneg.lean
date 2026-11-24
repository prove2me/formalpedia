-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_first_norm_real_nonneg
-- name    : Formalism.FourierDecayAlt.P.Cx2.first_norm_real_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:13:09.75019+00:00
-- url     : https://prove2.me/theorems/d2b365d6-1628-401c-a639-7dfa13c99bcc
-- title:
--   Cx2: first norm real nonneg
-- statement:
--   The Cx2 construction uses the first norm real nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L189-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L189-L231

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

theorem Formalism.FourierDecayAlt.P.Cx2.first_norm_real_nonneg (S : HidaSetting E Wp Wq) (hP : ThmPPos S) (ε : ℝ) (hε : 0 < ε) (i : ℕ)
    (hi : i ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (hκ : TB.PSDOn Y κ) (c : J.CV E) :
    ∃ x : ℝ, 0 ≤ x ∧ S.N1 ε i w.1 Y κ c = x := by sorry
