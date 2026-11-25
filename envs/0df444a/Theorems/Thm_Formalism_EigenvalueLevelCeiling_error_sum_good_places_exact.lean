-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_error_sum_good_places_exact
-- name    : Formalism.EigenvalueLevelCeiling.error_sum_good_places_exact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:22.452719+00:00
-- url     : https://prove2.me/theorems/27a1ee14-16e5-4b9b-9878-73f5e947baf9
-- title:
--   Eigenvalue Level Ceiling: error sum good places exact
-- statement:
--   The Eigenvalue Level Ceiling construction uses the error sum good places exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/AbsorbLocalConditionsOfExact.lean#L22-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/AbsorbLocalConditionsOfExact.lean#L22-L59

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_ErrSumGoodExact
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsComposeGeneral
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverP
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverPSqTail
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues

theorem Formalism.EigenvalueLevelCeiling.error_sum_good_places_exact : ErrSumGoodExact := by sorry
