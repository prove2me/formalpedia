-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_C_left
-- name    : Formalism.GradedWeylDivisibility.LFocks_C_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:36.974538+00:00
-- url     : https://prove2.me/theorems/ef769358-254a-4541-920b-5c69a5da692b
-- title:
--   Graded Weyl Divisibility: LFocks C left
-- statement:
--   The Graded Weyl Divisibility construction uses the LFocks C left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean#L26-L29

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

theorem Formalism.GradedWeylDivisibility.LFocks_C_left (a : ℂ) (g : MvPolynomial σ ℂ) :
    fockF (C a) g = a * star (constantCoeff g) := by sorry
