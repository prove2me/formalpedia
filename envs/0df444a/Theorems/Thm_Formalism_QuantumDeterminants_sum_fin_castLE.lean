-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_sum_fin_castLE
-- name    : Formalism.QuantumDeterminants.sum_fin_castLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:59.595668+00:00
-- url     : https://prove2.me/theorems/5c1e3b46-2da3-4c15-8dd6-56d70ff4e1f1
-- title:
--   Quantum Determinants: sum fin cast LE
-- statement:
--   The Quantum Determinants construction uses the sum fin cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L10-L18

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants

theorem Formalism.QuantumDeterminants.sum_fin_castLE {m l : ℕ} (h : l ≤ m) (f : Fin m → ℂ)
    (hf : ∀ j : Fin m, l ≤ j.val → f j = 0) :
    ∑ j, f j = ∑ j : Fin l, f (Fin.castLE h j) := by sorry
