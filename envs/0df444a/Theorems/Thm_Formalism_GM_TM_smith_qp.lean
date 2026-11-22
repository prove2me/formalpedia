-- Prove2me | Theorems.Thm_Formalism_GM_TM_smith_qp
-- name    : Formalism.GM.TM.smith_qp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:08.728907+00:00
-- url     : https://prove2.me/theorems/8da55d40-b28b-467b-8df7-48ca2fe8e395
-- title:
--   TM: smith qp
-- statement:
--   The TM construction uses the smith qp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L171-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L171-L216

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M Finset Matrix
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.GM.TM.smith_qp (hS : SmithZp) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ_[p]) :
    ∃ (U V : Matrix (Fin n) (Fin n) ℚ_[p]) (dg : Fin n → ℚ_[p]),
      (∀ x y, ‖U x y‖ ≤ 1) ∧ (∀ x y, ‖V x y‖ ≤ 1) ∧ ‖U.det‖ = 1 ∧ ‖V.det‖ = 1 ∧
        A = U * Matrix.diagonal dg * V := by sorry
