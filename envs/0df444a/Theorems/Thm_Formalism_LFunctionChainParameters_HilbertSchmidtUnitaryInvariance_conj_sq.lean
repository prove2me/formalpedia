-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_conj_sq
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.conj_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:10.628487+00:00
-- url     : https://prove2.me/theorems/6dad5d7b-80d3-475d-9c95-101ff42bf969
-- title:
--   Hilbert Schmidt Unitary Invariance: conj sq
-- statement:
--   The Hilbert Schmidt Unitary Invariance construction uses the conj sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L138-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L138-L142

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
variable {ι : Type} [Fintype ι] {D D' : ℕ} {d : ι → ℕ}

theorem Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.conj_sq (V : Matrix (Fin D') (Fin D) ℂ) (hV : Vᴴ * V = 1) (Q : Matrix (Fin D) (Fin D) ℂ) :
    (V * Q * Vᴴ) * (V * Q * Vᴴ) = V * (Q * Q) * Vᴴ := by sorry
