-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_psd_form_conj_rewrite
-- name    : Formalism.FourierDecayAlt.P.Jx1.psd_form_conj_rewrite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:34.851189+00:00
-- url     : https://prove2.me/theorems/75b1cdb5-b89e-482a-b0b4-19291a7b10e4
-- title:
--   Jx1: psd form conj rewrite
-- statement:
--   The Jx1 construction uses the psd form conj rewrite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L268-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L268-L273

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
variable {α : Type}

theorem Formalism.FourierDecayAlt.P.Jx1.psd_form_conj_rewrite (F : Finset α) (k : α → α → ℂ) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y) =
      ∑ x ∈ F, ∑ y ∈ F, conj ((fun z => conj (a z)) x) * k x y * (fun z => conj (a z)) y := by sorry
