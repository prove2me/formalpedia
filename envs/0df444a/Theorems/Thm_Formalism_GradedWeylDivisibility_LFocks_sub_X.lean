-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_sub_X
-- name    : Formalism.GradedWeylDivisibility.LFocks_sub_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:57:09.262804+00:00
-- url     : https://prove2.me/theorems/e2fe1686-8de6-4b9e-8d3d-e63bfe9ba31b
-- title:
--   Graded Weyl Divisibility: LFocks sub X
-- statement:
--   The Graded Weyl Divisibility construction uses the LFocks sub X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L35-L38

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

theorem Formalism.GradedWeylDivisibility.LFocks_sub_X (U : Matrix σ σ ℂ) (i : σ) :
    sub U (X i) = ∑ j, C (U i j) * X j := by sorry
