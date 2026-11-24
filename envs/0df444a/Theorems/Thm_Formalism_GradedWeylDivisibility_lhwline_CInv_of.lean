-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_CInv_of
-- name    : Formalism.GradedWeylDivisibility.lhwline_CInv_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:57:48.33081+00:00
-- url     : https://prove2.me/theorems/29235d6b-76dd-492d-a044-da740bde00ee
-- title:
--   Graded Weyl Divisibility: lhwline CInv of
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline CInv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L91-L96

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
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
variable {K : Type*} [Field K] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.lhwline_CInv_of (g : MvPolynomial (Fin r × Fin n) K)
    (h : ∀ l j : Fin n, l < j → ∀ c : K, colAdd K l j c g = g) :
    lhwline_CInv (fun x => eval x g) := by sorry
