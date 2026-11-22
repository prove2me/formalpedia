-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_GBasic_herm_bvec
-- name    : Formalism.QuantumDeterminants.GBasic.herm_bvec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:12:38.034414+00:00
-- url     : https://prove2.me/theorems/be8786e0-d999-49f8-9c99-6c6fdc51102b
-- title:
--   GBasic: herm bvec
-- statement:
--   The GBasic construction uses the herm bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L97-L99

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

theorem Formalism.QuantumDeterminants.GBasic.herm_bvec (k r : ℕ) (x y : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec x) (bvec y) = Hpk k r y x := by sorry
