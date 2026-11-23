-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_omegaF_eq
-- name    : Formalism.ELL.FormalGroupCubeJets.omegaF_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:31.755244+00:00
-- url     : https://prove2.me/theorems/857a1bc1-47d2-4e8a-b657-00efb8da9db1
-- title:
--   Formal Group Cube Jets: omega F eq
-- statement:
--   The Formal Group Cube Jets construction uses the omega F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L51-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L51-L51

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

theorem Formalism.ELL.FormalGroupCubeJets.omegaF_eq : omegaF F = Formalism.G.LogP.omegaF (FK F) := by sorry
