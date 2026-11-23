-- Prove2me | Theorems.Thm_Formalism_GM_TM_fockBil_apply
-- name    : Formalism.GM.TM.fockBil_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:37.491804+00:00
-- url     : https://prove2.me/theorems/556b5c12-0df1-4942-82ed-b026c353178b
-- title:
--   TM: fock Bil apply
-- statement:
--   The TM construction uses the fock Bil apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L868-L870
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L868-L870

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
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.GM.TM.fockBil_apply {N r : ℕ} (LL : Letters N)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (x y) :
    fockBil LL φ x y = fockN p LL (φ x) y := by sorry
