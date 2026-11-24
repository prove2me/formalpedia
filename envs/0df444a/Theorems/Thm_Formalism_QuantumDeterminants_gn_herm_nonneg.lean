-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_herm_nonneg
-- name    : Formalism.QuantumDeterminants.gn_herm_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:54.3305+00:00
-- url     : https://prove2.me/theorems/cc64a495-f0dc-4ed4-adb0-5119761aa9bd
-- title:
--   Quantum Determinants: gn herm nonneg
-- statement:
--   The Quantum Determinants construction uses the gn herm nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L105-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L105-L136

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

theorem Formalism.QuantumDeterminants.gn_herm_nonneg (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ)
    (h1 : ∀ a : Fin r, y (eI k r a) = y (esI k r a)) (h2 : y ⟨r + k, by omega⟩ = 0) :
    0 ≤ (herm (Hpk k r) y y).re := by sorry
