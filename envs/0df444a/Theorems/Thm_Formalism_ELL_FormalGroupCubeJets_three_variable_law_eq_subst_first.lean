-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_three_variable_law_eq_subst_first
-- name    : Formalism.ELL.FormalGroupCubeJets.three_variable_law_eq_subst_first
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:51.095619+00:00
-- url     : https://prove2.me/theorems/3d394b10-dc69-489a-9b01-ddb49989e905
-- title:
--   Formal Group Cube Jets: three variable law eq subst first
-- statement:
--   The Formal Group Cube Jets construction uses the three variable law eq subst first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L165-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L165-L173

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

theorem Formalism.ELL.FormalGroupCubeJets.three_variable_law_eq_subst_first : F3 F = (FK F).toPowerSeries.subst ![F2 F 1 2, MvPowerSeries.X 0] := by sorry
