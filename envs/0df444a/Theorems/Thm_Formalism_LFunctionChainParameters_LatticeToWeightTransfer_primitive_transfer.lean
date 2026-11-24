-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_primitive_transfer
-- name    : Formalism.LFunctionChainParameters.LatticeToWeightTransfer.primitive_transfer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:52.38408+00:00
-- url     : https://prove2.me/theorems/6f24dd88-6acf-41ee-8d1f-5b286bb79a44
-- title:
--   Lattice To Weight Transfer: primitive transfer
-- statement:
--   The Lattice To Weight Transfer construction uses the primitive transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SlopeInequalityOfLattices.lean#L65-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SlopeInequalityOfLattices.lean#L65-L80

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp cT : ℝ) (Q : ∀ u0, W u0 → PPrim ι m)

theorem Formalism.LFunctionChainParameters.LatticeToWeightTransfer.primitive_transfer : BridgePrim D Q := by sorry
