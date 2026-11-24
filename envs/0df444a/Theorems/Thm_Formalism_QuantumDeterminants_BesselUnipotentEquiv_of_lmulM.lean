-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BesselUnipotentEquiv_of_lmulM
-- name    : Formalism.QuantumDeterminants.BesselUnipotentEquiv.of_lmulM
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:47.327924+00:00
-- url     : https://prove2.me/theorems/e594b932-9e0b-4031-84a7-2959e30246dd
-- title:
--   Bessel Unipotent Equiv: of lmul M
-- statement:
--   The Bessel Unipotent Equiv construction uses the of lmul M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnipotentEquivHolds.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnipotentEquivHolds.lean#L63-L64

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BesselUnipotentEquiv
variable {k r : ℕ}

theorem Formalism.QuantumDeterminants.BesselUnipotentEquiv.of_lmulM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) :
    Matrix.of (lmulM a x) = a * Matrix.of x := by sorry
