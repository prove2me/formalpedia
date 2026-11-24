-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lpMinor_mem
-- name    : Formalism.GradedWeylDivisibility.lpMinor_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:59.304423+00:00
-- url     : https://prove2.me/theorems/07e3f333-5aac-43c7-9f4e-fbbdf9016f4e
-- title:
--   Graded Weyl Divisibility: lp Minor mem
-- statement:
--   The Graded Weyl Divisibility construction uses the lp Minor mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SumIcoTsubTelescope.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SumIcoTsubTelescope.lean#L91-L95

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

theorem Formalism.GradedWeylDivisibility.lpMinor_mem {R : Type*} [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    lpMinor R s hr hn ∈ dualWeyl R r n (initW n s) := by sorry
