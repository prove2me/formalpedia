-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_low_degree_power_series
-- name    : Formalism.CyclotomicNorms.low_degree_power_series
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:32.112793+00:00
-- url     : https://prove2.me/theorems/de7787c1-83dc-4f51-95ce-67e0a66b0d18
-- title:
--   Cyclotomic Norms: low degree power series
-- statement:
--   The Cyclotomic Norms construction uses the low degree power series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/LowDegreePowerSeries.lean#L41-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/LowDegreePowerSeries.lean#L41-L88

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_LowDegreePowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.CyclotomicNorms

theorem Formalism.CyclotomicNorms.low_degree_power_series : LowPowerSeries := by sorry
