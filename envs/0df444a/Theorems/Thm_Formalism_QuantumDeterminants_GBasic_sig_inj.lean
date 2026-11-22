-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_inj
-- name    : Formalism.QuantumDeterminants.GBasic.sig_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:10.112966+00:00
-- url     : https://prove2.me/theorems/1c09498e-3c20-4708-bb43-f4d276466f41
-- title:
--   GBasic: sig inj
-- statement:
--   The GBasic construction uses the sig inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L117-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L117-L123

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

theorem Formalism.QuantumDeterminants.GBasic.sig_inj (k r : ℕ) (i j : Fin (2 * r + k + 1)) : sig k r i = sig k r j ↔ i = j := by sorry
