-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_hsX
-- name    : Formalism.ELL.FormalGroupCubeJets.hsX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:57.744119+00:00
-- url     : https://prove2.me/theorems/9e373263-563a-4ef8-843e-cebec9b4cc88
-- title:
--   Formal Group Cube Jets: hs X
-- statement:
--   The Formal Group Cube Jets construction uses the hs X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L136-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L136-L137

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

theorem Formalism.ELL.FormalGroupCubeJets.hsX (i : Fin 3) : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) := by sorry
