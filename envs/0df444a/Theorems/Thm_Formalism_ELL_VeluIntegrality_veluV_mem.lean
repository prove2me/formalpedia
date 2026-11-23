-- Prove2me | Theorems.Thm_Formalism_ELL_VeluIntegrality_veluV_mem
-- name    : Formalism.ELL.VeluIntegrality.veluV_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:20:03.787796+00:00
-- url     : https://prove2.me/theorems/b73b326c-18d2-4e12-a078-a5eda19e8743
-- title:
--   Velu Integrality: velu V mem
-- statement:
--   The Velu Integrality construction uses the velu V mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluInt.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluInt.lean#L46-L54

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

theorem Formalism.ELL.VeluIntegrality.veluV_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluV W x y ∈ (ball : Subring K) := by sorry
