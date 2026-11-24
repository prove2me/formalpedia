-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_GBasic_PJP_apply
-- name    : Formalism.QuantumDeterminants.GBasic.PJP_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:21.411246+00:00
-- url     : https://prove2.me/theorems/5187c784-79a1-4e80-8fbb-56d09009ced0
-- title:
--   GBasic: PJP apply
-- statement:
--   The GBasic construction uses the PJP apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L142-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L142-L209

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

theorem Formalism.QuantumDeterminants.GBasic.PJP_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pk k r) i j = Hpk k r i j := by sorry
