-- Prove2me | Theorems.Thm_Formalism_ELL_CubeThreeAlt_subst_mem
-- name    : Formalism.ELL.CubeThreeAlt.subst_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:16.328777+00:00
-- url     : https://prove2.me/theorems/437ee84d-5161-407d-adac-0bc15db82a17
-- title:
--   Cube Three Alt: subst mem
-- statement:
--   The Cube Three Alt construction uses the subst mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L144-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L144-L160

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

theorem Formalism.ELL.CubeThreeAlt.subst_mem {τ : Type} [Finite τ] {f : MvPowerSeries τ K} (hf : f ∈ TT W τ)
    {a : τ → MvPowerSeries σ K} (ha : ∀ i, a i ∈ TT W σ) (ha0 : ∀ i, cc (a i) = 0) :
    MvPowerSeries.subst a f ∈ TT W σ := by sorry
