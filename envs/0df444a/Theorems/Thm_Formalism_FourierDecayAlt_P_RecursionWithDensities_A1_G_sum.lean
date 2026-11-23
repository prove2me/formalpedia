-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_G_sum
-- name    : Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.G_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:20.588784+00:00
-- url     : https://prove2.me/theorems/cc30b35a-7ca1-4699-af1e-35da9263e96a
-- title:
--   A1: G sum
-- statement:
--   The A1 construction uses the G sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L112-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L112-L159

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

theorem Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.G_sum (L : AddSubgroup E) (S : Finset E) (Th : E → α → α → ℂ) (R : Finset E)
    (hR : ∀ x ∈ R, ∀ y ∈ R, x - y ∈ L → x = y) :
    ∃ S' : Finset E, S' ⊆ S ∧ (∀ x ∈ S', ∃ t ∈ R, x - t ∈ L) ∧
      (∀ x ∈ S', ∀ y ∈ S', x - y ∈ L → x = y) ∧
      ∀ h h', ∑ t ∈ R, G L S Th (t : E ⧸ L) h h' = ∑ t₁ ∈ S', Th t₁ h h' := by sorry
