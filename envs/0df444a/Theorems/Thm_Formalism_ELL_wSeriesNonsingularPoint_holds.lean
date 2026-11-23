-- Prove2me | Theorems.Thm_Formalism_ELL_wSeriesNonsingularPoint_holds
-- name    : Formalism.ELL.wSeriesNonsingularPoint_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:39.633858+00:00
-- url     : https://prove2.me/theorems/eaccc281-1c76-4302-844a-85b958b76854
-- title:
--   ELL: w Series Nonsingular Point holds
-- statement:
--   The ELL construction uses the w Series Nonsingular Point holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WPoint.lean#L47-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WPoint.lean#L47-L116

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open WeierstrassPointSeriesTail

theorem Formalism.ELL.wSeriesNonsingularPoint_holds : WPoint := by sorry
