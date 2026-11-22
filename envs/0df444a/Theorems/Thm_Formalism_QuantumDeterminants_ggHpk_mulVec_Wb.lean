-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ggHpk_mulVec_Wb
-- name    : Formalism.QuantumDeterminants.ggHpk_mulVec_Wb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:21.460994+00:00
-- url     : https://prove2.me/theorems/3bb496da-d1c8-492c-8acd-d038d5626c63
-- title:
--   Quantum Determinants: gg Hpk mul Vec Wb
-- statement:
--   The Quantum Determinants construction uses the gg Hpk mul Vec Wb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/ReverseCauchySchwarzHolds.lean#L104-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/ReverseCauchySchwarzHolds.lean#L104-L122

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants

theorem Formalism.QuantumDeterminants.ggHpk_mulVec_Wb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v)
    (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = (if i.val = r + k then -1 else 1) * v i := by sorry
