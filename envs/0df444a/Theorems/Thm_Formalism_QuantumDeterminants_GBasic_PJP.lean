-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_GBasic_PJP
-- name    : Formalism.QuantumDeterminants.GBasic.PJP
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:08.325814+00:00
-- url     : https://prove2.me/theorems/3f0597dc-5dfa-47dc-91be-6a420ba00aef
-- title:
--   GBasic: PJP
-- statement:
--   The GBasic construction uses the PJP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L211-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L211-L213

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

theorem Formalism.QuantumDeterminants.GBasic.PJP (k r : ℕ) : (Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pk k r = Hpk k r := by sorry
