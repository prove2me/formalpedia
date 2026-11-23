-- Prove2me | Theorems.Thm_Formalism_ELL_CubeThreeAlt_wU_coeff_mem
-- name    : Formalism.ELL.CubeThreeAlt.wU_coeff_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:40.165867+00:00
-- url     : https://prove2.me/theorems/25c47797-c988-4ddf-84c1-7d1c0a083f71
-- title:
--   Cube Three Alt: w U coeff mem
-- statement:
--   The Cube Three Alt construction uses the w U coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L224-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L224-L226

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
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
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
variable {w : PowerSeries K}

theorem Formalism.ELL.CubeThreeAlt.wU_coeff_mem (hw : WFixed W w) (n : ℕ) : coeff n (wU w) ∈ Sadj W := by sorry
