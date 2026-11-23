-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_minor_RInv
-- name    : Formalism.GradedWeylDivisibility.lhwline_minor_RInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:32.410879+00:00
-- url     : https://prove2.me/theorems/1d33ca88-6505-4633-a3ff-6e87746d05a3
-- title:
--   Graded Weyl Divisibility: lhwline minor RInv
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline minor RInv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L241-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L241-L279

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

theorem Formalism.GradedWeylDivisibility.lhwline_minor_RInv (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    lhwline_RInv (fun x : Fin r × Fin n → K => eval x (lpMinor K s hr hn)) := by sorry
