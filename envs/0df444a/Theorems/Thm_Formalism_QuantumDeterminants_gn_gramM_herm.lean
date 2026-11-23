-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_gramM_herm
-- name    : Formalism.QuantumDeterminants.gn_gramM_herm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:33.241272+00:00
-- url     : https://prove2.me/theorems/10397995-80b8-47ea-a4cc-f005ecafb125
-- title:
--   Quantum Determinants: gn gram M herm
-- statement:
--   The Quantum Determinants construction uses the gn gram M herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L158-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L158-L163

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

theorem Formalism.QuantumDeterminants.gn_gramM_herm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : (gramM k r z z' g).IsHermitian := by sorry
