-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_pderiv_sub
-- name    : Formalism.GradedWeylDivisibility.LFocks_pderiv_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:43.146836+00:00
-- url     : https://prove2.me/theorems/e965c8db-8d73-4683-ae7c-bd02183e1aef
-- title:
--   Graded Weyl Divisibility: LFocks pderiv sub
-- statement:
--   The Graded Weyl Divisibility construction uses the LFocks pderiv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L68-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L68-L88

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
variable [DecidableEq σ]

theorem Formalism.GradedWeylDivisibility.LFocks_pderiv_sub (V : Matrix σ σ ℂ) (i : σ) (g : MvPolynomial σ ℂ) :
    pderiv i (sub V g) = ∑ j, C (V j i) * sub V (pderiv j g) := by sorry
