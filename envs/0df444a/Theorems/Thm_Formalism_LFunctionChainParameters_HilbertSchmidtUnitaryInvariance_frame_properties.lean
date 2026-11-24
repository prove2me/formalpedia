-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_properties
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.frame_properties
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:45.248504+00:00
-- url     : https://prove2.me/theorems/06284e5a-a1c2-4f85-9eca-2f2480787725
-- title:
--   Hilbert Schmidt Unitary Invariance: frame properties
-- statement:
--   The Hilbert Schmidt Unitary Invariance construction uses the frame properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L249-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L249-L262

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.frame_properties : FrameFacts := by sorry
