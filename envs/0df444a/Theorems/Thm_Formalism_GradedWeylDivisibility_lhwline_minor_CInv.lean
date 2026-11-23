-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_minor_CInv
-- name    : Formalism.GradedWeylDivisibility.lhwline_minor_CInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:46.320788+00:00
-- url     : https://prove2.me/theorems/f5e14bb6-fe53-44f3-92aa-10594ec08b0d
-- title:
--   Graded Weyl Divisibility: lhwline minor CInv
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline minor CInv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L281-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L281-L319

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
variable {K : Type} [Field K] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.lhwline_minor_CInv [Infinite K] (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    lhwline_CInv (fun x : Fin r × Fin n → K => eval x (lpMinor K s hr hn)) := by sorry
