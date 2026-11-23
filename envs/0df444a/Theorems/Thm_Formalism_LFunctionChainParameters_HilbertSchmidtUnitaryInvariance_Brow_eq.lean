-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Brow_eq
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Brow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:30:43.670219+00:00
-- url     : https://prove2.me/theorems/35b93efb-5509-4cd3-8e55-44b6bd22d4ad
-- title:
--   Hilbert Schmidt Unitary Invariance: Brow eq
-- statement:
--   The Hilbert Schmidt Unitary Invariance construction uses the Brow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L266-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L266-L269

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Brow_eq {ι : Type} {D D' : ℕ} {d : ι → ℕ} (W : Matrix (Fin D') (Fin D) ℂ)
    (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) :
    Brow W B = Btwist B (fun _ => 1) W (fun _ => 1) := by sorry
