-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_finite_out_smul
-- name    : Formalism.IndefR.Fin.Four.finite_out_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:36.268416+00:00
-- url     : https://prove2.me/theorems/5ab02591-067d-4015-af69-bf1ff9ff3588
-- title:
--   Four: finite out smul
-- statement:
--   The Four construction uses the finite out smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourUniq.lean#L39-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourUniq.lean#L39-L59

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
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

theorem Formalism.IndefR.Fin.Four.finite_out_smul (H : AddSubgroup W) {k : ℕ} [Finite (Qt (k * k) H)] (htf : ∀ t : W, k • t = 0 → t = 0) :
    {q : W ⧸ smulSub k H | k • q.out ∈ H}.Finite := by sorry
