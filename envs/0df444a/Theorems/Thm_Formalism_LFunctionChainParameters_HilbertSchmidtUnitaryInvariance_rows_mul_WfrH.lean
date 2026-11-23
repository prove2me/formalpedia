-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_rows_mul_WfrH
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.rows_mul_WfrH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:31:09.787398+00:00
-- url     : https://prove2.me/theorems/9c6837d6-b4a2-4835-b226-860f0bff5ba6
-- title:
--   Hilbert Schmidt Unitary Invariance: rows mul Wfr H
-- statement:
--   The Hilbert Schmidt Unitary Invariance construction uses the rows mul Wfr H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L227-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L227-L234

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.rows_mul_WfrH {a b : ℕ} (X : Matrix (Fin a) (Fin Dall) ℂ) (X1 : Matrix (Fin b) (Fin Dall) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    (Matrix.fromRows X X1).submatrix finSumFinEquiv.symm id * (Wfr J J1)ᴴ
      = (Matrix.fromBlocks (X * J) (X * J1) (X1 * J) (X1 * J1)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by sorry
