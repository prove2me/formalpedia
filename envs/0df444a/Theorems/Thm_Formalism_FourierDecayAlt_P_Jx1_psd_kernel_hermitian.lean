-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_psd_kernel_hermitian
-- name    : Formalism.FourierDecayAlt.P.Jx1.psd_kernel_hermitian
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:09.829088+00:00
-- url     : https://prove2.me/theorems/efec5b82-0de9-4c49-9ae9-4ec913f5aa57
-- title:
--   Jx1: psd kernel hermitian
-- statement:
--   The Jx1 construction uses the psd kernel hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L275-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L275-L309

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

theorem Formalism.FourierDecayAlt.P.Jx1.psd_kernel_hermitian (F : Finset α) (k : α → α → ℂ) (h : A5.IsPSD F k) :
    ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y) := by sorry
