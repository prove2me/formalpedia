-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_formalSum
-- name    : Formalism.ELL.WeierstrassChordSeries.constantCoeff_formalSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:52.093812+00:00
-- url     : https://prove2.me/theorems/074655d1-6e29-4e74-b0e9-545c58084ae2
-- title:
--   Weierstrass Chord Series: constant Coeff formal Sum
-- statement:
--   The Weierstrass Chord Series construction uses the constant Coeff formal Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L534-L535
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L534-L535

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

theorem Formalism.ELL.WeierstrassChordSeries.constantCoeff_formalSum (hw : WFixed W w) : cc (F2 W w) = 0 := by sorry
