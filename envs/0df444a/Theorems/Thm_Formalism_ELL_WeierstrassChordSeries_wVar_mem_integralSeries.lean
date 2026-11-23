-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_wVar_mem_integralSeries
-- name    : Formalism.ELL.WeierstrassChordSeries.wVar_mem_integralSeries
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:10.927607+00:00
-- url     : https://prove2.me/theorems/a8239d0b-efae-4270-b670-2d8f368a30e5
-- title:
--   Weierstrass Chord Series: w Var mem integral Series
-- statement:
--   The Weierstrass Chord Series construction uses the w Var mem integral Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L608-L614
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L608-L614

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

theorem Formalism.ELL.WeierstrassChordSeries.wVar_mem_integralSeries (hw : WFixed W w) (i : Fin 2) : Wi w i ∈ T W := by sorry
