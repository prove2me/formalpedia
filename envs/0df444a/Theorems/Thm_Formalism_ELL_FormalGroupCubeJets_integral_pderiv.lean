-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_pderiv
-- name    : Formalism.ELL.FormalGroupCubeJets.integral_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:57.507516+00:00
-- url     : https://prove2.me/theorems/b2c67db0-1e70-4440-a0e5-1c061a87b995
-- title:
--   Formal Group Cube Jets: integral pderiv
-- statement:
--   The Formal Group Cube Jets construction uses the integral pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L26-L33

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

theorem Formalism.ELL.FormalGroupCubeJets.integral_pderiv {σ : Type} (i : σ) {f : MvPowerSeries σ K} (hf : IntegralMv f) :
    IntegralMv (MvPowerSeries.pderiv K i f) := by sorry
