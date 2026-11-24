-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_Ik_finite
-- name    : Formalism.IndefR.Fin.Four.Ik_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:13.539117+00:00
-- url     : https://prove2.me/theorems/ba8ea681-8819-448f-937a-f7a3f4539ec8
-- title:
--   Four: Ik finite
-- statement:
--   The Four construction uses the Ik finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L18-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L18-L36

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
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

theorem Formalism.IndefR.Fin.Four.Ik_finite {L Y : AddSubgroup W} {k : ℕ} [Finite (Qt (k * k) (L ⊓ Y))]
    (htf : ∀ t : W, k • t = 0 → t = 0) : Finite (Ik L Y k) := by sorry
