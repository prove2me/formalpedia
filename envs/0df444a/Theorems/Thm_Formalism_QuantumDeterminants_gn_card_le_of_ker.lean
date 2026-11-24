-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_card_le_of_ker
-- name    : Formalism.QuantumDeterminants.gn_card_le_of_ker
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:19:02.84402+00:00
-- url     : https://prove2.me/theorems/a3b5e99f-f2e6-4a00-aa32-aad7466a8a4f
-- title:
--   Quantum Determinants: gn card le of ker
-- statement:
--   The Quantum Determinants construction uses the gn card le of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L9-L15

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

theorem Formalism.QuantumDeterminants.gn_card_le_of_ker {S : Type*} [Fintype S] {m : ℕ} (f : (S → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hf : ∀ v, f v = 0 → v = 0) : Fintype.card S ≤ m := by sorry
