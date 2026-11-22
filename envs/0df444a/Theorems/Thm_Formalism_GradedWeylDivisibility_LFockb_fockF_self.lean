-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_LFockb_fockF_self
-- name    : Formalism.GradedWeylDivisibility.LFockb_fockF_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:23.681799+00:00
-- url     : https://prove2.me/theorems/4e2d7660-950d-4b3b-acf6-fb558ba07266
-- title:
--   Graded Weyl Divisibility: LFockb fock F self
-- statement:
--   The Graded Weyl Divisibility construction uses the LFockb fock F self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFockbLemmas.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFockbLemmas.lean#L12-L20

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)

theorem Formalism.GradedWeylDivisibility.LFockb_fockF_self {σ : Type*} (f : MvPolynomial σ ℂ) :
    fockF f f = ((∑ m ∈ f.support, Complex.normSq (f.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by sorry
