-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_mcol_inv
-- name    : Formalism.GradedWeylDivisibility.lhwline_mcol_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:32.581379+00:00
-- url     : https://prove2.me/theorems/900c52cf-5dba-4673-8d45-2c15138215f5
-- title:
--   Graded Weyl Divisibility: lhwline mcol inv
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline mcol inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L130-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L130-L146

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

theorem Formalism.GradedWeylDivisibility.lhwline_mcol_inv (φ : (Fin r × Fin n → K) → K) (hφ : lhwline_CInv φ) (q : Fin n)
    (c : Fin n → K) (x : Fin r × Fin n → K) (S : Finset (Fin n)) (hS : ∀ j ∈ S, q < j) :
    φ (lhwline_mcol q S c x) = φ x := by sorry
