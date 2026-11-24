-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Pk_star
-- name    : Formalism.QuantumDeterminants.GBasic.Pk_star
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:07.454382+00:00
-- url     : https://prove2.me/theorems/8b7ff80f-66f1-4066-a706-2918815050ad
-- title:
--   GBasic: Pk star
-- statement:
--   The GBasic construction uses the Pk star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L138-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L138-L140

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

theorem Formalism.QuantumDeterminants.GBasic.Pk_star (k r : ℕ) (i j : Fin (2 * r + k + 1)) : star (Pk k r i j) = Pk k r i j := by sorry
