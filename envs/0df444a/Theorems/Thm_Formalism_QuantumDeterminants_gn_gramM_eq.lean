-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_gramM_eq
-- name    : Formalism.QuantumDeterminants.gn_gramM_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:07.740163+00:00
-- url     : https://prove2.me/theorems/105cf140-1f9a-4d4b-ae0a-d8b18026bf10
-- title:
--   Quantum Determinants: gn gram M eq
-- statement:
--   The Quantum Determinants construction uses the gn gram M eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L143-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L143-L151

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

theorem Formalism.QuantumDeterminants.gn_gramM_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    gramM k r z z' g = (gnB k r z z' g)ᴴ * Hpk k r * gnB k r z z' g := by sorry
