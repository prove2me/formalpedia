-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_lowPowerSeries
-- name    : Formalism.CyclotomicNorms.lowPowerSeries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:47.504792+00:00
-- url     : https://prove2.me/theorems/8f2271af-f318-49fa-8ba0-9ce9755084df
-- title:
--   Cyclotomic Norms: low Power Series
-- statement:
--   The Cyclotomic Norms construction uses the low Power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/SubstitutionAdaptive.lean#L9-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/SubstitutionAdaptive.lean#L9-L9

import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_AdaptiveSubstitutionBound
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_LowDegreePowerSeries
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_CyclotomicNorms_SubstitutionAdaptive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CyclotomicNorms

theorem Formalism.CyclotomicNorms.lowPowerSeries : LowPowerSeries := by sorry
