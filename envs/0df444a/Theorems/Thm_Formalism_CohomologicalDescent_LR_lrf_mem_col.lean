-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_mem_col
-- name    : Formalism.CohomologicalDescent.LR.lrf_mem_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:54.082492+00:00
-- url     : https://prove2.me/theorems/0f325f7b-0ac9-4bb5-ac46-f0a271346ac9
-- title:
--   LR: lrf mem col
-- statement:
--   The LR construction uses the lrf mem col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L226-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L226-L244

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.CohomologicalDescent.LR.lrf_mem_col (s : Fin n) (l : Fin r × Fin r × (Fin r × Fin n)) :
    (l ∈ (List.finRange r).filterMap fun a =>
      if h : s.val < a.val ∧ s.val < r then some ((⟨s.val, h.2⟩ : Fin r), a, (a, s)) else none) ↔
      l.1.val = s.val ∧ s.val < l.2.1.val ∧ l.2.2 = (l.2.1, s) := by sorry
