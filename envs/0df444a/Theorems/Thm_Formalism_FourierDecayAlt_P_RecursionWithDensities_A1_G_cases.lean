-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_G_cases
-- name    : Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.G_cases
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:30.051341+00:00
-- url     : https://prove2.me/theorems/4eb3d480-eda4-4b72-82b3-1ffdfc1570a9
-- title:
--   A1: G cases
-- statement:
--   The A1 construction uses the G cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L99-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L99-L110

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
variable {α : Type}
variable {E : Type} [AddCommGroup E]

theorem Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.G_cases (L : AddSubgroup E) (S : Finset E) (Th : E → α → α → ℂ) (c : E ⧸ L) :
    ((¬ ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c) ∧ G L S Th c = fun _ _ => 0) ∨
      ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c ∧ G L S Th c = Th t₁ := by sorry
