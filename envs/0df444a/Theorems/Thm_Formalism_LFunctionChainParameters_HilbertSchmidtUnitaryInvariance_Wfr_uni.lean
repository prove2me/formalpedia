-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Wfr_uni
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Wfr_uni
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:49:48.119333+00:00
-- url     : https://prove2.me/theorems/f75208c0-039e-4ae8-be14-83c3042d9607
-- title:
--   Hilbert Schmidt Unitary Invariance: Wfr uni
-- statement:
--   The Hilbert Schmidt Unitary Invariance construction uses the Wfr uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L236-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L236-L245

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
variable {Dall D D1 : ℕ}

theorem Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Wfr_uni (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (h : OrthFrame J J1) : IsUni (Wfr J J1) := by sorry
