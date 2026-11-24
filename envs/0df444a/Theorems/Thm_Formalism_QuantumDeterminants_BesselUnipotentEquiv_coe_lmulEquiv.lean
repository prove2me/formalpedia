-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BesselUnipotentEquiv_coe_lmulEquiv
-- name    : Formalism.QuantumDeterminants.BesselUnipotentEquiv.coe_lmulEquiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:48.015799+00:00
-- url     : https://prove2.me/theorems/0aaf74a4-c9f5-4572-b198-ca0d176a755d
-- title:
--   Bessel Unipotent Equiv: coe lmul Equiv
-- statement:
--   The Bessel Unipotent Equiv construction uses the coe lmul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnipotentEquivHolds.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnipotentEquivHolds.lean#L60-L61

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

theorem Formalism.QuantumDeterminants.BesselUnipotentEquiv.coe_lmulEquiv (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) :
    ⇑(lmulEquiv (k := k) (r := r) a ha) = lmulM a := by sorry
