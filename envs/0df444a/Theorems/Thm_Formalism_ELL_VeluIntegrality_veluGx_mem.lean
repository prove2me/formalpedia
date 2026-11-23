-- Prove2me | Theorems.Thm_Formalism_ELL_VeluIntegrality_veluGx_mem
-- name    : Formalism.ELL.VeluIntegrality.veluGx_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:59.671038+00:00
-- url     : https://prove2.me/theorems/8b8ae0e4-3f6f-4477-8925-f3d524fabcc9
-- title:
--   Velu Integrality: velu Gx mem
-- statement:
--   The Velu Integrality construction uses the velu Gx mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluInt.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluInt.lean#L31-L37

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

theorem Formalism.ELL.VeluIntegrality.veluGx_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluGx W x y ∈ (ball : Subring K) := by sorry
