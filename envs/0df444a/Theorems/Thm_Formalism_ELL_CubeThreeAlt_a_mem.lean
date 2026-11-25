-- Prove2me | Theorems.Thm_Formalism_ELL_CubeThreeAlt_a_mem
-- name    : Formalism.ELL.CubeThreeAlt.a_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:24:28.783963+00:00
-- url     : https://prove2.me/theorems/249f8773-9aea-485d-a4a5-f4b23bf1c976
-- title:
--   Cube Three Alt: a mem
-- statement:
--   The Cube Three Alt construction uses the a mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L198-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L198-L199

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

theorem Formalism.ELL.CubeThreeAlt.a_mem (i : Fin 5) : ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆] i ∈ Sadj W := by sorry
