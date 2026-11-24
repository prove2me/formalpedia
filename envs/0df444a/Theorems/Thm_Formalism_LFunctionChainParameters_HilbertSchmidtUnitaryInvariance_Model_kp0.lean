-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Model_kp0
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model.kp0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:16.610478+00:00
-- url     : https://prove2.me/theorems/ac5c6c64-4c5d-4401-9869-56700e1e0a39
-- title:
--   Model: kp0
-- statement:
--   The Model construction uses the kp0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L387-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L387-L388

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model.kp0 (u u' : Fin 20) : Kp (d := fun _ => 2) P0 (fun _ => (1 : ℝ)) u u' = 1 := by sorry
