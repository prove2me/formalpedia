-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_Hpk_mulVec
-- name    : Formalism.QuantumDeterminants.gn_Hpk_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:24.843715+00:00
-- url     : https://prove2.me/theorems/0fc92401-e949-46d7-87ae-a16d43002201
-- title:
--   Quantum Determinants: gn Hpk mul Vec
-- statement:
--   The Quantum Determinants construction uses the gn Hpk mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L67-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L67-L99

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

theorem Formalism.QuantumDeterminants.gn_Hpk_mulVec (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ y) i = if _h : i.val < r ∨ r + k < i.val then y ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -y i else y i := by sorry
