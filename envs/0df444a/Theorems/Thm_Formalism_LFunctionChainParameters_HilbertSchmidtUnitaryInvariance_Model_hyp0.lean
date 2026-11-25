-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Model_hyp0
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model.hyp0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:39.578144+00:00
-- url     : https://prove2.me/theorems/16dffbfe-847f-44d4-ad80-d36b29e3f5a7
-- title:
--   Model: hyp0
-- statement:
--   The Model construction uses the hyp0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L408-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L408-L427

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module NumberField
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
open Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model

theorem Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model.hyp0 :
    ChainHyp (d := fun _ => 2) (r := r0) P0 (fun u => En (r0 u)) (fun _ => 1) c0 V0 U0 J0 modelEmbedding A0 1
      (fun _ => 1) 2 (1 / 20) 0 0 0 (1 / 40) (1 / 2) 1 1 := by sorry
