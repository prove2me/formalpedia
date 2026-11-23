-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_pderiv_two_variable_law_other
-- name    : Formalism.ELL.FormalGroupCubeJets.pderiv_two_variable_law_other
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:43.5107+00:00
-- url     : https://prove2.me/theorems/c03569ca-6fdb-4594-ba14-b244489f72dc
-- title:
--   Formal Group Cube Jets: pderiv two variable law other
-- statement:
--   The Formal Group Cube Jets construction uses the pderiv two variable law other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L147-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L147-L150

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

theorem Formalism.ELL.FormalGroupCubeJets.pderiv_two_variable_law_other (a b k : Fin 3) (ha : a ≠ k) (hb : b ≠ k) :
    MvPowerSeries.pderiv K k (F2 F a b) = 0 := by sorry
