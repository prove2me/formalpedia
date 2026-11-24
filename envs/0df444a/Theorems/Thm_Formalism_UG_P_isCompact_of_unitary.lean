-- Prove2me | Theorems.Thm_Formalism_UG_P_isCompact_of_unitary
-- name    : Formalism.UG.P.isCompact_of_unitary
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:31:27.311542+00:00
-- url     : https://prove2.me/theorems/4787ffcc-c56d-4db9-ae3e-98d54d1e0dcc
-- title:
--   P: is Compact of unitary
-- statement:
--   The P construction uses the is Compact of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Upqcpt.lean#L16-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Upqcpt.lean#L16-L41

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.isCompact_of_unitary {T : Set (Matrix n n ℂ)} (hT : IsClosed T)
    (hU : ∀ M ∈ T, star M * M = 1) : IsCompact T := by sorry
