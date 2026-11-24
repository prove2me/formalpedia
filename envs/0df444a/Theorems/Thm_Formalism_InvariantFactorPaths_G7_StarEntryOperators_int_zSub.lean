-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_int_zSub
-- name    : Formalism.InvariantFactorPaths.G7.StarEntryOperators.int_zSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:40.814083+00:00
-- url     : https://prove2.me/theorems/783257d0-0162-41b8-b935-3eb9ffba03ae
-- title:
--   Star Entry Operators: int z Sub
-- statement:
--   The Star Entry Operators construction uses the int z Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L163-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L163-L177

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact opInt)
open Formalism.GrowthSums (gamP rhoP)
open Formalism.InvariantFactorPaths.G7.StarEntryOperators

theorem Formalism.InvariantFactorPaths.G7.StarEntryOperators.int_zSub {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}
    (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (hξ : ∀ s a, ‖ξ s a‖ ≤ 1)
    (x : ZV ν r0 r1) : Integral (zSub (r1 := r1) TT ξ x) := by sorry
