-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_hbsb
-- name    : Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts.hbsb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:10.637111+00:00
-- url     : https://prove2.me/theorems/978f3390-042e-4a3a-af2e-af81fb8a9cfe
-- title:
--   Facts: hbsb
-- statement:
--   The Facts construction uses the hbsb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L235-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L235-L238

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
variable {P : Par} {e K z u E X S sb v w8 : ℝ} (F : Facts P e K z u E X S sb v w8)
include F

theorem Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts.hbsb : 100 * K * (E ^ 4 * P.x ^ 4) * (X * S) * sb ≤ P.b := by sorry
