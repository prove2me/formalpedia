-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_sub_comp
-- name    : Formalism.GradedWeylDivisibility.LFocks_sub_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:33.274544+00:00
-- url     : https://prove2.me/theorems/bd077901-e525-400a-9b58-ed046bd48f94
-- title:
--   Graded Weyl Divisibility: LFocks sub comp
-- statement:
--   The Graded Weyl Divisibility construction uses the LFocks sub comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L54-L60

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
variable {σ : Type*} [Fintype σ]

theorem Formalism.GradedWeylDivisibility.LFocks_sub_comp (A B : Matrix σ σ ℂ) :
    (sub A).comp (sub B) = sub (B * A) := by sorry
