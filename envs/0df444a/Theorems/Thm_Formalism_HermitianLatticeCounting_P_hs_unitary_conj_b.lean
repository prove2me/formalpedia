-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_hs_unitary_conj_b
-- name    : Formalism.HermitianLatticeCounting.P.hs_unitary_conj_b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:51.987142+00:00
-- url     : https://prove2.me/theorems/0872058e-2759-4af0-a105-2536fddb9664
-- title:
--   P: hs unitary conj b
-- statement:
--   The P construction uses the hs unitary conj b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L20-L30

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

theorem Formalism.HermitianLatticeCounting.P.hs_unitary_conj_b {N : ℕ} (k X : Matrix (Fin N) (Fin N) ℂ) (hk : kᴴ * k = 1) :
    hs (k * X * kᴴ) = hs X := by sorry
