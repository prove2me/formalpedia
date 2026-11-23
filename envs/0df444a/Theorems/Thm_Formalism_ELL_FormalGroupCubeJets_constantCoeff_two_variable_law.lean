-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_constantCoeff_two_variable_law
-- name    : Formalism.ELL.FormalGroupCubeJets.constantCoeff_two_variable_law
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:13.852129+00:00
-- url     : https://prove2.me/theorems/6f640563-d095-4c01-939d-6cfed0fc99b1
-- title:
--   Formal Group Cube Jets: constant Coeff two variable law
-- statement:
--   The Formal Group Cube Jets construction uses the constant Coeff two variable law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L139-L141

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

theorem Formalism.ELL.FormalGroupCubeJets.constantCoeff_two_variable_law (a b : Fin 3) : MvPowerSeries.constantCoeff (F2 F a b) = 0 := by sorry
