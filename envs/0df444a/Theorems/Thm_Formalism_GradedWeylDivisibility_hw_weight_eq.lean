-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_hw_weight_eq
-- name    : Formalism.GradedWeylDivisibility.hw_weight_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T18:24:48.822645+00:00
-- url     : https://prove2.me/theorems/7fb56791-2ec3-4998-a4c7-d38a5cba5e4f
-- title:
--   Graded Weyl Divisibility: hw weight eq
-- statement:
--   The Graded Weyl Divisibility construction uses the hw weight eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SumIcoTsubTelescope.lean#L28-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SumIcoTsubTelescope.lean#L28-L89

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
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

theorem Formalism.GradedWeylDivisibility.hw_weight_eq {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    (∑ s : Fin n, (ν s - nuNext ν s) • initW n (s.val + 1)) = ν := by sorry
