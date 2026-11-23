-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_omegaX
-- name    : Formalism.ELL.FormalGroupCubeJets.integral_omegaX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:23.330203+00:00
-- url     : https://prove2.me/theorems/3550e54e-a107-4e49-8a78-de33b448cfe7
-- title:
--   Formal Group Cube Jets: integral omega X
-- statement:
--   The Formal Group Cube Jets construction uses the integral omega X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L67-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L67-L78

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

theorem Formalism.ELL.FormalGroupCubeJets.integral_omegaX (j : Fin 3) :
    IntegralMv ((omegaF F).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K)) := by sorry
