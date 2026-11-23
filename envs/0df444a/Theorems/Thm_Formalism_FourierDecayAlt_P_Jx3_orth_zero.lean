-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_orth_zero
-- name    : Formalism.FourierDecayAlt.P.Jx3.orth_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:29.616255+00:00
-- url     : https://prove2.me/theorems/ce3b2438-dc4d-469e-a665-75f814e91fa3
-- title:
--   Jx3: orth zero
-- statement:
--   The Jx3 construction uses the orth zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L46-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L46-L102

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
open InfinitePlace

theorem Formalism.FourierDecayAlt.P.Jx3.orth_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (z : CV E)
    (h : ∀ t : E, inner ℝ z (cemb E t) = 0) : z = 0 := by sorry
