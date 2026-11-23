-- Prove2me | Theorems.Thm_Formalism_ELL_CubeThreeAlt_chordCoeffCubic_inversionDenom_inv
-- name    : Formalism.ELL.CubeThreeAlt.chordCoeffCubic_inversionDenom_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:10.435923+00:00
-- url     : https://prove2.me/theorems/3bcd03b2-024f-4988-86ca-243c7ab55281
-- title:
--   Cube Three Alt: chord Coeff Cubic inversion Denom inv
-- statement:
--   The Cube Three Alt construction uses the chord Coeff Cubic inversion Denom inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L228-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L228-L259

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

theorem Formalism.ELL.CubeThreeAlt.chordCoeffCubic_inversionDenom_inv (hw : WFixed W w) : C3 W w * (C3 W w)⁻¹ = 1 ∧ dd W w * (dd W w)⁻¹ = 1 ∧
    (C3 W w)⁻¹ ∈ T W ∧ (dd W w)⁻¹ ∈ T W := by sorry
