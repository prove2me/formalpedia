-- Prove2me | Theorems.Thm_Formalism_ELL_CubeThreeAlt_pair
-- name    : Formalism.ELL.CubeThreeAlt.pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:01.65282+00:00
-- url     : https://prove2.me/theorems/df598f8d-e9f9-4630-9d82-62293043cf5a
-- title:
--   Cube Three Alt: pair
-- statement:
--   The Cube Three Alt construction uses the pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L278-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L278-L329

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

theorem Formalism.ELL.CubeThreeAlt.pair [Finite σ] (hw : WFixed W w) (a b : MvPowerSeries σ K) (ha : cc a = 0) (hb : cc b = 0)
    (haT : a ∈ TT W σ) (hbT : b ∈ TT W σ) :
    ∃ l n z A B : MvPowerSeries σ K,
      (b - a) * l = w.subst b - w.subst a ∧ n = w.subst a - l * a ∧
      chordCoeffCubicAt W l * A = 1 ∧ z = -a - b - chordCoeffQuadraticAt W l n * A ∧
      DDs W l n z * B = 1 ∧ MvPowerSeries.subst ![a, b] (F2 W w) = z * B ∧
      cc l = 0 ∧ l ∈ TT W σ ∧ A ∈ TT W σ ∧ B ∈ TT W σ := by sorry
