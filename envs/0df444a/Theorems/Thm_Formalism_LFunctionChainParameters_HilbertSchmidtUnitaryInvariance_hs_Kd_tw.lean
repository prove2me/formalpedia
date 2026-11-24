-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_hs_Kd_tw
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.hs_Kd_tw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:52.127818+00:00
-- url     : https://prove2.me/theorems/22ff3bd6-8461-47c2-83d6-e41acd805b1a
-- title:
--   Hilbert Schmidt Unitary Invariance: hs Kd tw
-- statement:
--   The Hilbert Schmidt Unitary Invariance construction uses the hs Kd tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L104-L109

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.hs_Kd_tw (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (c : ι → ℂ)
    (V : Matrix (Fin D') (Fin D) ℂ) (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ)
    (hc : ∀ u, c u ≠ 0) (hV : Vᴴ * V = 1) (hU : ∀ u, IsUni (U u)) (u : ι) :
    hsSq (Kd (Btwist B c V U) (gaTw ga c) u - 1) = hsSq (Kd B ga u - 1) := by sorry
