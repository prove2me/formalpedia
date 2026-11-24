-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_sum_pos
-- name    : Formalism.QuantumDeterminants.gn_sum_pos
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:19:13.529454+00:00
-- url     : https://prove2.me/theorems/72841acc-584e-4792-b9fc-880e6b842c54
-- title:
--   Quantum Determinants: gn sum pos
-- statement:
--   The Quantum Determinants construction uses the gn sum pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L268-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L268-L288

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
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

theorem Formalism.QuantumDeterminants.gn_sum_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℝ)
    (v : {i // 0 < lam i} → ℂ) (hv : v ≠ 0) :
    0 < ∑ i, lam i * Complex.normSq ((gnExt (fun i => 0 < lam i) *ᵥ v) i) := by sorry
