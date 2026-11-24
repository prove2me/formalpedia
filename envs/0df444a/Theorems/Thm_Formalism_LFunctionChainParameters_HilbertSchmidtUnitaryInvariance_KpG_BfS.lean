-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_KpG_BfS
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.KpG_BfS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:05.38882+00:00
-- url     : https://prove2.me/theorems/d0485b75-0525-4ce7-a6e6-f1be2719a836
-- title:
--   Hilbert Schmidt Unitary Invariance: Kp G Bf S
-- statement:
--   The Hilbert Schmidt Unitary Invariance construction uses the Kp G Bf S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L454-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L454-L466

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.KpG_BfS {ι : Type} [Fintype ι] {Dall D D1 : ℕ} {d : ι → ℕ}
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) (h : OrthFrame J J1)
    (g : ι → ℝ) (u u' : ι) :
    MatrixLatticeEstimates.KpG (BfS Pf c V J J1) g u u' = Kp (Btwist Pf c V (fun _ => 1)) g u u' := by sorry
