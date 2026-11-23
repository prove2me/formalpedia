-- Prove2me | Theorems.Thm_Formalism_ELL_VeluIntegrality_mem_ball
-- name    : Formalism.ELL.VeluIntegrality.mem_ball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:17.075078+00:00
-- url     : https://prove2.me/theorems/a90387df-a59d-4843-b662-0fa8cf470e0b
-- title:
--   Velu Integrality: mem ball
-- statement:
--   The Velu Integrality construction uses the mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluInt.lean#L29-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluInt.lean#L29-L29

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluInt
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
open Formalism Formalism.ELL
open Formalism.ELL.VeluIntegrality
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.VeluIntegrality.mem_ball {x : K} : x ∈ (ball : Subring K) ↔ ‖x‖ ≤ 1 := by sorry
