-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_hs_sq_trace_b
-- name    : Formalism.HermitianLatticeCounting.P.hs_sq_trace_b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:45.190977+00:00
-- url     : https://prove2.me/theorems/a30ec953-0727-47b5-ab0e-11852204bc7b
-- title:
--   P: hs sq trace b
-- statement:
--   The P construction uses the hs sq trace b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L12-L18

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

theorem Formalism.HermitianLatticeCounting.P.hs_sq_trace_b {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) :
    ((∑ a, ∑ b, ‖Y a b‖ ^ 2 : ℝ) : ℂ) = (Yᴴ * Y).trace := by sorry
