-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_const
-- name    : Formalism.ELL.FormalGroupCubeJets.Dj_const
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:55.248177+00:00
-- url     : https://prove2.me/theorems/4c0aefc5-492a-47c9-84b6-a696f154ff17
-- title:
--   Formal Group Cube Jets: Dj const
-- statement:
--   The Formal Group Cube Jets construction uses the Dj const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L96-L99

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

theorem Formalism.ELL.FormalGroupCubeJets.Dj_const (j : Fin 3) (ψ : PowerSeries K) {A : MvPowerSeries (Fin 3) K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hdA : MvPowerSeries.pderiv K j A = 0) :
    Dj F j (ψ.subst A) = 0 := by sorry
