-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_pderiv_zero_subst_three_variable_law
-- name    : Formalism.ELL.FormalGroupCubeJets.pderiv_zero_subst_three_variable_law
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:10.118639+00:00
-- url     : https://prove2.me/theorems/59a43b0d-7a5e-4137-a7d7-4ee06a15d834
-- title:
--   Formal Group Cube Jets: pderiv zero subst three variable law
-- statement:
--   The Formal Group Cube Jets construction uses the pderiv zero subst three variable law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L175-L177

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

theorem Formalism.ELL.FormalGroupCubeJets.pderiv_zero_subst_three_variable_law (ψ : PowerSeries K) : Dj F 0 (ψ.subst (F3 F)) = (invD F ψ).subst (F3 F) := by sorry
