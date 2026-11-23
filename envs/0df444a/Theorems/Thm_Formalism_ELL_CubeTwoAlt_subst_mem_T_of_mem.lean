-- Prove2me | Theorems.Thm_Formalism_ELL_CubeTwoAlt_subst_mem_T_of_mem
-- name    : Formalism.ELL.CubeTwoAlt.subst_mem_T_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:55.643066+00:00
-- url     : https://prove2.me/theorems/c2e32869-7bd6-4078-99f9-1f1bb27cf142
-- title:
--   Cube Two Alt: subst mem T of mem
-- statement:
--   The Cube Two Alt construction uses the subst mem T of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L65-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L65-L82

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
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
open Formalism.ELL.CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff

theorem Formalism.ELL.CubeTwoAlt.subst_mem_T_of_mem {W : WeierstrassCurve K} {f : MvPowerSeries (Fin 2) K} (hf : f ∈ T W)
    {a : Fin 2 → MvPowerSeries (Fin 2) K} (ha : ∀ i, a i ∈ T W) (h0 : ∀ i, cc (a i) = 0) :
    f.subst a ∈ T W := by sorry
