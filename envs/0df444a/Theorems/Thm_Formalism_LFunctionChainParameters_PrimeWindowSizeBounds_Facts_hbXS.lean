-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_hbXS
-- name    : Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts.hbXS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:56.501841+00:00
-- url     : https://prove2.me/theorems/2996f420-df66-4f81-8798-3cbaa152a8ca
-- title:
--   Facts: hb XS
-- statement:
--   The Facts construction uses the hb XS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L233-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L233-L233

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

theorem Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts.hbXS : 100 * K * (E ^ 4 * P.x ^ 4) * (X * S) ≤ P.b := by sorry
