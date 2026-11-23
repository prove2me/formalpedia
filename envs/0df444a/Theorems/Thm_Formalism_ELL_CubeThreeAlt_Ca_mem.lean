-- Prove2me | Theorems.Thm_Formalism_ELL_CubeThreeAlt_Ca_mem
-- name    : Formalism.ELL.CubeThreeAlt.Ca_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:28.544114+00:00
-- url     : https://prove2.me/theorems/8c2bca27-9e23-44a1-984e-3dbaf9234623
-- title:
--   Cube Three Alt: Ca mem
-- statement:
--   The Cube Three Alt construction uses the Ca mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L201-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L201-L208

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

theorem Formalism.ELL.CubeThreeAlt.Ca_mem : (MvPowerSeries.C W.a₁ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₂ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₃ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₄ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₆ : MvPowerSeries σ K) ∈ TT W σ := by sorry
