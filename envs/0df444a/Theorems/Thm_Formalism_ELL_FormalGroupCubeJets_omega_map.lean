-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_omega_map
-- name    : Formalism.ELL.FormalGroupCubeJets.omega_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:38.633427+00:00
-- url     : https://prove2.me/theorems/8c73721f-fc0f-44c3-8e75-c69d06dedd36
-- title:
--   Formal Group Cube Jets: omega map
-- statement:
--   The Formal Group Cube Jets construction uses the omega map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L56-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L56-L65

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

theorem Formalism.ELL.FormalGroupCubeJets.omega_map : omegaF F = PowerSeries.map (unitBall K).subtype
    (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries (unitBall K)), 0]
      (MvPowerSeries.pderiv (unitBall K) 1 F.toPowerSeries)) := by sorry
