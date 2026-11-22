-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_C_mul_right
-- name    : Formalism.GradedWeylDivisibility.LFocks_C_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:33.512832+00:00
-- url     : https://prove2.me/theorems/3f753e7d-5b14-46b1-bd14-b992c43b1396
-- title:
--   Graded Weyl Divisibility: LFocks C mul right
-- statement:
--   The Graded Weyl Divisibility construction uses the LFocks C mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L21-L24

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

theorem Formalism.GradedWeylDivisibility.LFocks_C_mul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (C c * g) = star c * fockF f g := by sorry
