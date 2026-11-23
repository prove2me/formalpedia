-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_sub
-- name    : Formalism.ELL.FormalGroupCubeJets.Dj_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:17.293275+00:00
-- url     : https://prove2.me/theorems/a4f9ced7-3326-4545-8e77-618d8e82ef8a
-- title:
--   Formal Group Cube Jets: Dj sub
-- statement:
--   The Formal Group Cube Jets construction uses the Dj sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L87-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L87-L88

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

theorem Formalism.ELL.FormalGroupCubeJets.Dj_sub (j : Fin 3) (a b : MvPowerSeries (Fin 3) K) : Dj F j (a - b) = Dj F j a - Dj F j b := by sorry
