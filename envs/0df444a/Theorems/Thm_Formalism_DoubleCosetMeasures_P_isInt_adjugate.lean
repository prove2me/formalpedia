-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_isInt_adjugate
-- name    : Formalism.DoubleCosetMeasures.P.isInt_adjugate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:50.490558+00:00
-- url     : https://prove2.me/theorems/6c1eac4c-43fd-4f99-b602-58e78b34fa64
-- title:
--   P: is Int adjugate
-- statement:
--   The P construction uses the is Int adjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsIntOfLatOfLe.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsIntOfLatOfLe.lean#L89-L95

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
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

theorem Formalism.DoubleCosetMeasures.P.isInt_adjugate {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) :
    IsInt R A.adjugate := by sorry
