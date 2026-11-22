-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_hi
-- name    : Formalism.QuantumDeterminants.GBasic.sig_hi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:04.637269+00:00
-- url     : https://prove2.me/theorems/370a732f-ddd5-4721-a144-9f11939f9dc8
-- title:
--   GBasic: sig hi
-- statement:
--   The GBasic construction uses the sig hi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L105-L107

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
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
open Formalism.QuantumDeterminants.GBasic

theorem Formalism.QuantumDeterminants.GBasic.sig_hi (k r : ℕ) (i : Fin (2 * r + k + 1)) (h : r + k < i.val) :
    (sig k r i).val = 2 * r + k - i.val := by sorry
