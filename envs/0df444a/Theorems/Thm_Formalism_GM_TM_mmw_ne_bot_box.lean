-- Prove2me | Theorems.Thm_Formalism_GM_TM_mmw_ne_bot_box
-- name    : Formalism.GM.TM.mmw_ne_bot_box
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:36.825087+00:00
-- url     : https://prove2.me/theorems/4f35691b-327f-4459-beac-1d02eb1ca713
-- title:
--   TM: mmw ne bot box
-- statement:
--   The TM construction uses the mmw ne bot box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L144-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L144-L163

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
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.GM.TM.mmw_ne_bot_box {K r : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (w : Fin r → ℤ) (h : MMw p LLw J M ρ w ≠ ⊥) :
    w ∈ Fintype.piFinset (fun _ : Fin r => Icc (-(LLw.total : ℤ)) LLw.total) := by sorry
