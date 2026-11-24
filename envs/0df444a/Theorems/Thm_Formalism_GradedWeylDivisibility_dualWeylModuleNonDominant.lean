-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylModuleNonDominant
-- name    : Formalism.GradedWeylDivisibility.dualWeylModuleNonDominant
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:53.34316+00:00
-- url     : https://prove2.me/theorems/94da7256-03d5-4b39-be8e-2e3edad81c8f
-- title:
--   Graded Weyl Divisibility: dual Weyl Module Non Dominant
-- statement:
--   The Graded Weyl Divisibility construction uses the dual Weyl Module Non Dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L121-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L121-L132

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
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
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.dualWeylModuleNonDominant : DualWeylNonDom := by sorry
