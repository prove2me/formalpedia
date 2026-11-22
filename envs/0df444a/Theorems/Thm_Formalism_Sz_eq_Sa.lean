-- Prove2me | Theorems.Thm_Formalism_Sz_eq_Sa
-- name    : Formalism.Sz_eq_Sa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:13.869656+00:00
-- url     : https://prove2.me/theorems/781d0276-3e3b-4515-8484-dc35708ecace
-- title:
--   Formalism: Sz eq Sa
-- statement:
--   The Formalism construction uses the Sz eq Sa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MeasurableGchi.lean#L12-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MeasurableGchi.lean#L12-L12

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

theorem Formalism.Sz_eq_Sa : Sz = Sa (fun n => Λ n) := by sorry
