-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_sum_neg
-- name    : Formalism.QuantumDeterminants.gn_sum_neg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:19:10.468329+00:00
-- url     : https://prove2.me/theorems/29609b5a-86dd-4bfc-9931-544c830f850f
-- title:
--   Quantum Determinants: gn sum neg
-- statement:
--   The Quantum Determinants construction uses the gn sum neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L246-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L246-L266

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

theorem Formalism.QuantumDeterminants.gn_sum_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℝ)
    (v : {i // lam i < 0} → ℂ) (hv : v ≠ 0) :
    ∑ i, lam i * Complex.normSq ((gnExt (fun i => lam i < 0) *ᵥ v) i) < 0 := by sorry
