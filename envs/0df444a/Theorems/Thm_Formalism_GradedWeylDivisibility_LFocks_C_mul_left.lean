-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_C_mul_left
-- name    : Formalism.GradedWeylDivisibility.LFocks_C_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:30.947802+00:00
-- url     : https://prove2.me/theorems/7f17ed3c-967d-425a-a54e-ec41b1364004
-- title:
--   Graded Weyl Divisibility: LFocks C mul left
-- statement:
--   The Graded Weyl Divisibility construction uses the LFocks C mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L14-L19

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {σ : Type*}

theorem Formalism.GradedWeylDivisibility.LFocks_C_mul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (C c * f) g = c * fockF f g := by sorry
