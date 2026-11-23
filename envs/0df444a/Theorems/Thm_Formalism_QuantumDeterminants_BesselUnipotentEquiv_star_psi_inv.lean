-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BesselUnipotentEquiv_star_psi_inv
-- name    : Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:25.00442+00:00
-- url     : https://prove2.me/theorems/7756d31c-ce89-4e38-8e23-c66bd0198d10
-- title:
--   Bessel Unipotent Equiv: star psi inv
-- statement:
--   The Bessel Unipotent Equiv construction uses the star psi inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnipotentEquivHolds.lean#L46-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnipotentEquivHolds.lean#L46-L58

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

theorem Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z)
    (n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hn : n ∈ Nset k r) :
    star (psi k r z c n⁻¹) = psi k r z c n := by sorry
