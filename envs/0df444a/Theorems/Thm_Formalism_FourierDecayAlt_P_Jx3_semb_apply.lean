-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_semb_apply
-- name    : Formalism.FourierDecayAlt.P.Jx3.semb_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:33:30.468933+00:00
-- url     : https://prove2.me/theorems/715d595b-d77b-4fb1-9331-00f3a08aa970
-- title:
--   Jx3: semb apply
-- statement:
--   The Jx3 construction uses the semb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L36-L37

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

theorem Formalism.FourierDecayAlt.P.Jx3.semb_apply (E : Type) [Field E] [NumberField E] (c : ℝ) (t : E) : semb E c t = c • cemb E t := by sorry
