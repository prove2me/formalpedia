-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_Hpk_mulVec_lo
-- name    : Formalism.QuantumDeterminants.gn_Hpk_mulVec_lo
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:04.044922+00:00
-- url     : https://prove2.me/theorems/52e41230-3355-4011-8e16-78b99623eb41
-- title:
--   Quantum Determinants: gn Hpk mul Vec lo
-- statement:
--   The Quantum Determinants construction uses the gn Hpk mul Vec lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L101-L103

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

theorem Formalism.QuantumDeterminants.gn_Hpk_mulVec_lo (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hi : i.val < r) : (Hpk k r *ᵥ y) i = y ⟨2 * r + k - i.val, by omega⟩ := by sorry
