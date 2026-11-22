-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
-- name    : Formalism.QuantumDeterminants.GBasic.Hpk_herm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:41:49.162661+00:00
-- url     : https://prove2.me/theorems/baec3123-ed0d-457a-9971-7dfc22d096c8
-- title:
--   GBasic: Hpk herm
-- statement:
--   The GBasic construction uses the Hpk herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L215-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L215-L222

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

theorem Formalism.QuantumDeterminants.GBasic.Hpk_herm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by sorry
