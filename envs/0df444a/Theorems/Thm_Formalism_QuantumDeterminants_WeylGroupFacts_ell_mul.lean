-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_ell_mul
-- name    : Formalism.QuantumDeterminants.WeylGroupFacts.ell_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:31.903469+00:00
-- url     : https://prove2.me/theorems/94cd0db1-ca48-4e2e-ace3-00de5eba9b0a
-- title:
--   Weyl Group Facts: ell mul
-- statement:
--   The Weyl Group Facts construction uses the ell mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L206-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L206-L228

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
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
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}

theorem Formalism.QuantumDeterminants.WeylGroupFacts.ell_mul (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) : ell k r z (g * h) = ell k r z g + ell k r z h := by sorry
