-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_mid
-- name    : Formalism.QuantumDeterminants.GBasic.sig_mid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:10:37.513164+00:00
-- url     : https://prove2.me/theorems/736da0c9-f069-41c0-b0a9-1ca41f56edd4
-- title:
--   GBasic: sig mid
-- statement:
--   The GBasic construction uses the sig mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L109-L112

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

theorem Formalism.QuantumDeterminants.GBasic.sig_mid (k r : ℕ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    sig k r i = i := by sorry
