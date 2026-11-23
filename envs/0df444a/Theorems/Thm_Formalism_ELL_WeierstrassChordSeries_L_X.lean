-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_X
-- name    : Formalism.ELL.WeierstrassChordSeries.L_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:05.975911+00:00
-- url     : https://prove2.me/theorems/f4f3f5de-c8d3-43df-95f4-b3ed544670c6
-- title:
--   Weierstrass Chord Series: L X
-- statement:
--   The Weierstrass Chord Series construction uses the L X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L429-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L429-L435

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

theorem Formalism.ELL.WeierstrassChordSeries.L_X (i j : Fin 2) : (L i) (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = if i = j then 1 else 0 := by sorry
