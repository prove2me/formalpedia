-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_jn_nonneg
-- name    : Formalism.FourierDecayAlt.P.Jx7.jn_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:52.75321+00:00
-- url     : https://prove2.me/theorems/2ff40675-7312-4801-85ec-988ed3ceebc0
-- title:
--   Jx7: jn nonneg
-- statement:
--   The Jx7 construction uses the jn nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L542-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L542-L558

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder

theorem Formalism.FourierDecayAlt.P.Jx7.jn_nonneg {E W : Type} [Field E] (D : TB.Data E W) (jn : ℝ) (hG : D.GramPSD) (hE : D.EstE jn) :
    0 ≤ jn := by sorry
