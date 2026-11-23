-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_chain
-- name    : Formalism.ELL.FormalGroupCubeJets.integral_chain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:37.79215+00:00
-- url     : https://prove2.me/theorems/0b8be2ea-3235-41dc-8bf6-3fa8e0ff89f8
-- title:
--   Formal Group Cube Jets: integral chain
-- statement:
--   The Formal Group Cube Jets construction uses the integral chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L234-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L234-L243

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

theorem Formalism.ELL.FormalGroupCubeJets.integral_chain (hN : NPderiv.{u}) (φ : PowerSeries K) (h : InN (triDiff F φ)) (k : ℕ) :
    IntegralMv ((Dj F 0)^[k] (Dj F 0 (Dj F 1 (Dj F 2 (triDiff F φ))))) := by sorry
