-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_two_variable_law_one_two_eq
-- name    : Formalism.ELL.FormalGroupCubeJets.two_variable_law_one_two_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:14.242856+00:00
-- url     : https://prove2.me/theorems/3d50e2e5-8d0e-4334-aa17-7095f3792338
-- title:
--   Formal Group Cube Jets: two variable law one two eq
-- statement:
--   The Formal Group Cube Jets construction uses the two variable law one two eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L161-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L161-L163

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

theorem Formalism.ELL.FormalGroupCubeJets.two_variable_law_one_two_eq : F2 F 1 2 = (FK F).toPowerSeries.subst ![MvPowerSeries.X 2, MvPowerSeries.X 1] := by sorry
