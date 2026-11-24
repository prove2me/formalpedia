-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_sq_sum_fin_b
-- name    : Formalism.HermitianLatticeCounting.P.sq_sum_fin_b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:16.663714+00:00
-- url     : https://prove2.me/theorems/ee2a3f3f-d215-4f0e-bbd0-e9387139a788
-- title:
--   P: sq sum fin b
-- statement:
--   The P construction uses the sq sum fin b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L247-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L247-L267

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)

theorem Formalism.HermitianLatticeCounting.P.sq_sum_fin_b {a : ℕ} (j : Fin a → ℕ) :
    (∑ x, j x) ^ 2 = ∑ x, j x ^ 2 + 2 * ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y := by sorry
