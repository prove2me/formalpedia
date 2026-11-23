-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_mono
-- name    : Formalism.DoubleCosetMeasures.P.Phase.mul_mono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:45:26.616112+00:00
-- url     : https://prove2.me/theorems/68e50e98-2a28-4d40-a7e0-d6af5474d8e9
-- title:
--   Phase: mul mono
-- statement:
--   The Phase construction uses the mul mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L126-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L126-L133

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

theorem Formalism.DoubleCosetMeasures.P.Phase.mul_mono (s : List ℕ) (f : Fin s.sum → K) (M : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : (M * mono s f) a c = M a (revF s c) * f (revF s c) := by sorry
