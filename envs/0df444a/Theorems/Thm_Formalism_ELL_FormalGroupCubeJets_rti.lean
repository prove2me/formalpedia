-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_rti
-- name    : Formalism.ELL.FormalGroupCubeJets.rti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:52.357983+00:00
-- url     : https://prove2.me/theorems/59a662d0-7ba2-45aa-ba31-01908629b375
-- title:
--   Formal Group Cube Jets: rti
-- statement:
--   The Formal Group Cube Jets construction uses the rti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L108-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L108-L131

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

theorem Formalism.ELL.FormalGroupCubeJets.rti (ψ : PowerSeries K) {A : MvPowerSeries (Fin 3) K}
    (hA : MvPowerSeries.constantCoeff A = 0) (j : Fin 3) (hdA : MvPowerSeries.pderiv K j A = 0) :
    Dj F j (ψ.subst ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j])) =
      (invD F ψ).subst ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j]) := by sorry
