-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_exp_sq_psd_b
-- name    : Formalism.HermitianLatticeCounting.P.exp_sq_psd_b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:32.904324+00:00
-- url     : https://prove2.me/theorems/ee2d6726-5839-44e8-b3d3-036a24a49454
-- title:
--   P: exp sq psd b
-- statement:
--   The P construction uses the exp sq psd b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L42-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L42-L94

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

theorem Formalism.HermitianLatticeCounting.P.exp_sq_psd_b {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) :
    ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ)
        - NormedSpace.exp X * NormedSpace.exp X).PosSemidef := by sorry
