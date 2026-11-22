-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sgn_sig
-- name    : Formalism.QuantumDeterminants.GBasic.sgn_sig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:14.829115+00:00
-- url     : https://prove2.me/theorems/b95da4da-a27e-4e21-8853-d3c9679eaaf9
-- title:
--   GBasic: sgn sig
-- statement:
--   The GBasic construction uses the sgn sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean#L84-L88

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

theorem Formalism.QuantumDeterminants.GBasic.sgn_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r (sig k r i) = sgn k r i := by sorry
