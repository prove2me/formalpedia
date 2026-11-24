-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_elim_inv
-- name    : Formalism.GradedWeylDivisibility.lhwline_elim_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:23:05.152231+00:00
-- url     : https://prove2.me/theorems/4cd0e512-5181-43c6-86c9-e76530049a11
-- title:
--   Graded Weyl Divisibility: lhwline elim inv
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline elim inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L164-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L164-L172

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

theorem Formalism.GradedWeylDivisibility.lhwline_elim_inv (φ : (Fin r × Fin n → K) → K) (hR : lhwline_RInv φ) (hC : lhwline_CInv φ)
    (k : ℕ) (x : Fin r × Fin n → K) : φ (lhwline_elim k x) = φ x := by sorry
