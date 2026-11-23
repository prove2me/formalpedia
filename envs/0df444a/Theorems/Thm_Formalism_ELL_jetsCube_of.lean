-- Prove2me | Theorems.Thm_Formalism_ELL_jetsCube_of
-- name    : Formalism.ELL.jetsCube_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:19.445428+00:00
-- url     : https://prove2.me/theorems/66ec68aa-3b94-46af-bc1b-4aaad8a35c30
-- title:
--   ELL: jets Cube of
-- statement:
--   The ELL construction uses the jets Cube of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L254-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L254-L261

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL

theorem Formalism.ELL.jetsCube_of (hN : Formalism.ELL.NPderiv.{u}) : Formalism.ELL.JetsCube.{u} := by sorry
