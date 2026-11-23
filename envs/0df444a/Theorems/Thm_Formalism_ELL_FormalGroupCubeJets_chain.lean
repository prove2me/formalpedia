-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_chain
-- name    : Formalism.ELL.FormalGroupCubeJets.chain
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:09.085565+00:00
-- url     : https://prove2.me/theorems/909ea1c1-9998-430f-b507-f2a2b48c2f59
-- title:
--   Formal Group Cube Jets: chain
-- statement:
--   The Formal Group Cube Jets construction uses the chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L224-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L224-L232

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

theorem Formalism.ELL.FormalGroupCubeJets.chain (φ : PowerSeries K) (k : ℕ) :
    (Dj F 0)^[k] (Dj F 0 (Dj F 1 (Dj F 2 (triDiff F φ)))) = ((invD F)^[k + 3] φ).subst (F3 F) := by sorry
