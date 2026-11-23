-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_pt_iff
-- name    : Formalism.FourierDecayAlt.P.Jx1.pt_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:26.083476+00:00
-- url     : https://prove2.me/theorems/7123ff04-7f13-4231-b04d-59dcb91778ed
-- title:
--   Jx1: pt iff
-- statement:
--   The Jx1 construction uses the pt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L170-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L170-L220

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

theorem Formalism.FourierDecayAlt.P.Jx1.pt_iff [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (p : TB.Pt E) :
    ∀ n, p ∈ TA.PT (fun j s => Sg (j - s + 1) s) n ↔ TB.level p = n ∧ Cnd Sg p := by sorry
