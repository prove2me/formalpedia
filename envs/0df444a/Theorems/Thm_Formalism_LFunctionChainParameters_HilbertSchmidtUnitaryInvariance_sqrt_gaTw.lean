-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_sqrt_gaTw
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.sqrt_gaTw
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:37.531799+00:00
-- url     : https://prove2.me/theorems/9bb478ee-689f-4d58-bf26-b06bfa371f4d
-- title:
--   Hilbert Schmidt Unitary Invariance: sqrt ga Tw
-- statement:
--   The Hilbert Schmidt Unitary Invariance construction uses the sqrt ga Tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L56-L63

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.sqrt_gaTw (ga : ι → ℝ) (c : ι → ℂ) (hc : ∀ u, c u ≠ 0) (u u' : ι) :
    Real.sqrt (gaTw ga c u * gaTw ga c u') = Real.sqrt (ga u * ga u') / (‖c u‖ * ‖c u'‖) := by sorry
