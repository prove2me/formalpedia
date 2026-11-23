-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_linearCoeff_thirdParam
-- name    : Formalism.ELL.WeierstrassChordSeries.linearCoeff_thirdParam
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:00.336584+00:00
-- url     : https://prove2.me/theorems/6bb1a68a-32c4-4cd7-a57c-98279f920018
-- title:
--   Weierstrass Chord Series: linear Coeff third Param
-- statement:
--   The Weierstrass Chord Series construction uses the linear Coeff third Param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L523-L526
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L523-L526

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

theorem Formalism.ELL.WeierstrassChordSeries.linearCoeff_thirdParam (hw : WFixed W w) (i : Fin 2) : (L i) (z3 W w) = -1 := by sorry
