-- Prove2me | Theorems.Thm_Formalism_rint_Gz
-- name    : Formalism.rint_Gz
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:55.17285+00:00
-- url     : https://prove2.me/theorems/dcc8ff1b-4feb-40c1-99fe-7eb0621a8cf8
-- title:
--   Formalism: rint Gz
-- statement:
--   The Formalism construction uses the rint Gz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MeasurableGchi.lean#L39-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MeasurableGchi.lean#L39-L52

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

theorem Formalism.rint_Gz (h3 : MellinSgen) (h5 : MellinElem) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => Gz x * x ^ (-σ - 1)) (Ioi 1) := by sorry
