-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WRPres_isOpen_omX
-- name    : Formalism.QuantumDeterminants.WRPres.isOpen_omX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:10:50.848879+00:00
-- url     : https://prove2.me/theorems/15aa5019-fbe7-46bc-85b7-05aa989e53fd
-- title:
--   WRPres: is Open om X
-- statement:
--   The WRPres construction uses the is Open om X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRPres.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRPres.lean#L13-L16

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WRPres
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.QuantumDeterminants.WRPres.isOpen_omX (m : ℕ) : IsOpen (OmX m) := by sorry
