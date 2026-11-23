-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r2_basis_of_r1
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.r2_basis_of_r1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:31.333118+00:00
-- url     : https://prove2.me/theorems/75608c6f-72ee-4e21-9ef0-24796ed63c1c
-- title:
--   Height Descent Minors: r2 basis of r1
-- statement:
--   The Height Descent Minors construction uses the r2 basis of r1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1051-L1055
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1051-L1055

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors

theorem Formalism.CohomologicalDescent.HeightDescentMinors.r2_basis_of_r1 (h1 : R1) (hb : BasisGeneral) : PowerSeriesFreeBasis := by sorry
