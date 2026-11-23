-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mono_mul
-- name    : Formalism.DoubleCosetMeasures.P.Phase.mono_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:05.661552+00:00
-- url     : https://prove2.me/theorems/0f13ddd7-79c2-49e0-936c-0bfe8decf31d
-- title:
--   Phase: mono mul
-- statement:
--   The Phase construction uses the mono mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L117-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L117-L124

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
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
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]

theorem Formalism.DoubleCosetMeasures.P.Phase.mono_mul (s : List ℕ) (f : Fin s.sum → K) (M : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : (mono s f * M) a c = f a * M (revF s a) c := by sorry
