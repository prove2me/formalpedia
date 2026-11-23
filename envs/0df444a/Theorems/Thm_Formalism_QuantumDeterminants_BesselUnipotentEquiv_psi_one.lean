-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BesselUnipotentEquiv_psi_one
-- name    : Formalism.QuantumDeterminants.BesselUnipotentEquiv.psi_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:46.84101+00:00
-- url     : https://prove2.me/theorems/a2cd131c-33a1-4e9b-a7f3-2e7b2f6552d4
-- title:
--   Bessel Unipotent Equiv: psi one
-- statement:
--   The Bessel Unipotent Equiv construction uses the psi one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnipotentEquivHolds.lean#L31-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnipotentEquivHolds.lean#L31-L44

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

theorem Formalism.QuantumDeterminants.BesselUnipotentEquiv.psi_one (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z) :
    psi k r z c 1 = 1 := by sorry
