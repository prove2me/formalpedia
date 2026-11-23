-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_inv_mem_integralSeries
-- name    : Formalism.ELL.WeierstrassChordSeries.inv_mem_integralSeries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:59.026557+00:00
-- url     : https://prove2.me/theorems/4f7e23fb-e22d-4506-8bfa-3236924abbd8
-- title:
--   Weierstrass Chord Series: inv mem integral Series
-- statement:
--   The Weierstrass Chord Series construction uses the inv mem integral Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L564-L582
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L564-L582

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
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
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}

theorem Formalism.ELL.WeierstrassChordSeries.inv_mem_integralSeries {φ : MvPowerSeries (Fin 2) K} (h : φ ∈ T W) (h0 : cc φ ≠ 0)
    (hi : (cc φ)⁻¹ ∈ Sadj W) : φ⁻¹ ∈ T W := by sorry
