-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_constantCoeff_sub
-- name    : Formalism.GradedWeylDivisibility.LFocks_constantCoeff_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:44.297204+00:00
-- url     : https://prove2.me/theorems/2df314a4-7df1-4064-ae08-f04057963f85
-- title:
--   Graded Weyl Divisibility: LFocks constant Coeff sub
-- statement:
--   The Graded Weyl Divisibility construction uses the LFocks constant Coeff sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L45-L52

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

theorem Formalism.GradedWeylDivisibility.LFocks_constantCoeff_sub (U : Matrix σ σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (sub U g) = constantCoeff g := by sorry
