-- Prove2me | Theorems.Thm_Formalism_ELL_CubeThreeAlt_psubst_mem
-- name    : Formalism.ELL.CubeThreeAlt.psubst_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:03.126028+00:00
-- url     : https://prove2.me/theorems/9b474a9e-9dab-4dd3-8586-70e9b2a0609d
-- title:
--   Cube Three Alt: psubst mem
-- statement:
--   The Cube Three Alt construction uses the psubst mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L162-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L162-L172

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

theorem Formalism.ELL.CubeThreeAlt.psubst_mem {f : PowerSeries K} (hf : ∀ n, coeff n f ∈ Sadj W)
    {a : MvPowerSeries σ K} (ha : a ∈ TT W σ) (ha0 : cc a = 0) : f.subst a ∈ TT W σ := by sorry
