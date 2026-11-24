-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_finite_nsmul_out
-- name    : Formalism.IndefR.Fin.Four.finite_nsmul_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:59.108548+00:00
-- url     : https://prove2.me/theorems/54b09e33-9593-47c2-b05f-65e207f39e48
-- title:
--   Four: finite nsmul out
-- statement:
--   The Four construction uses the finite nsmul out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L113-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L113-L133

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {L X : AddSubgroup W}

theorem Formalism.IndefR.Fin.Four.finite_nsmul_out (H : AddSubgroup W) {k : ℕ} [Finite (Qt k H)]
    (htf : ∀ t : W, k • t = 0 → t = 0) : {q : W ⧸ H | k • q.out ∈ H}.Finite := by sorry
