-- Prove2me | Theorems.Thm_Formalism_measurable_Gz
-- name    : Formalism.measurable_Gz
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:49.993642+00:00
-- url     : https://prove2.me/theorems/98f52b97-d466-42a3-847d-fd83cd9fa313
-- title:
--   Formalism: measurable Gz
-- statement:
--   The Formalism construction uses the measurable Gz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MeasurableGchi.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MeasurableGchi.lean#L26-L30

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open ArithmeticFunction

theorem Formalism.measurable_Gz (h3 : MellinSgen) : Measurable Gz := by sorry
