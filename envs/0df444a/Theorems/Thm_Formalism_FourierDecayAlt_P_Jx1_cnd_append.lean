-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_cnd_append
-- name    : Formalism.FourierDecayAlt.P.Jx1.cnd_append
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:16.008335+00:00
-- url     : https://prove2.me/theorems/7090298a-4307-4a9a-819b-53f302fdfecc
-- title:
--   Jx1: cnd append
-- statement:
--   The Jx1 construction uses the cnd append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L142-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L142-L165

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
variable {E : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.Jx1.cnd_append (Sg : ℕ → ℕ → Finset E) (h : TB.Pt E) (s : ℕ) (t : E) :
    Cnd Sg (h ++ [(s, t)]) ↔ Cnd Sg h ∧ 1 ≤ s ∧ t ∈ Sg (TB.level h + 1) s := by sorry
