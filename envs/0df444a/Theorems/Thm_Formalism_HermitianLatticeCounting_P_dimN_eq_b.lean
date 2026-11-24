-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_dimN_eq_b
-- name    : Formalism.HermitianLatticeCounting.P.dimN_eq_b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:59.75594+00:00
-- url     : https://prove2.me/theorems/085b047d-1dab-483f-9a3b-0cacde071516
-- title:
--   P: dim N eq b
-- statement:
--   The P construction uses the dim N eq b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L269-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L269-L278

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

theorem Formalism.HermitianLatticeCounting.P.dimN_eq_b {a : ℕ} (j : Fin a → ℕ) (n0 : ℕ) :
    dimN j n0 = 4 * (∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y) + ∑ x, j x ^ 2
      + 2 * (∑ x, j x) * n0 := by sorry
