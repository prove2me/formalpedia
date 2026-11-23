-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_X
-- name    : Formalism.ELL.FormalGroupCubeJets.Dj_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:44.870301+00:00
-- url     : https://prove2.me/theorems/ec47123a-7840-49cd-a2ce-6b47c4b8bf92
-- title:
--   Formal Group Cube Jets: Dj X
-- statement:
--   The Formal Group Cube Jets construction uses the Dj X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L101-L106

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

theorem Formalism.ELL.FormalGroupCubeJets.Dj_X (j : Fin 3) (ψ : PowerSeries K) :
    Dj F j (ψ.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K)) =
      (invD F ψ).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) := by sorry
