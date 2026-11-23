-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_step0
-- name    : Formalism.ELL.FormalGroupCubeJets.step0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:52.024481+00:00
-- url     : https://prove2.me/theorems/ed2a315a-ac8c-4673-8574-16552acd4ac7
-- title:
--   Formal Group Cube Jets: step0
-- statement:
--   The Formal Group Cube Jets construction uses the step0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L217-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L217-L222

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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupCubeJets
open MvPowerSeries Formalism.G Formalism.G.LogCR Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable (F : FormalGroup (unitBall K))

theorem Formalism.ELL.FormalGroupCubeJets.step0 (φ : PowerSeries K) : Dj F 0
    ((invD F (invD F φ)).subst (F3 F) - (invD F (invD F φ)).subst (F2 F 1 2)) =
    (invD F (invD F (invD F φ))).subst (F3 F) := by sorry
