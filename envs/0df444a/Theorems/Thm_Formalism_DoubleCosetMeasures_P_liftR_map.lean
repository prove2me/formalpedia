-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_liftR_map
-- name    : Formalism.DoubleCosetMeasures.P.liftR_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:42.03626+00:00
-- url     : https://prove2.me/theorems/1a8100e0-a3f6-46f1-b1fb-c0cf643b7f6b
-- title:
--   P: lift R map
-- statement:
--   The P construction uses the lift R map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L20-L23

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem Formalism.DoubleCosetMeasures.P.liftR_map (M : Matrix (Fin n) (Fin n) K) (hM : IsInt R M) :
    (liftR R M hM).map R.subtype = M := by sorry
